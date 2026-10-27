module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNCtx

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFW

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [hA x, hB x]

namespace Ctx

variable {V T N : Subgroup G} {X : Type} [Group X] [Finite X] {π : ↥N →* X} {Lb : Subgroup X}
variable (c : Ctx V T N π Lb)
include c

theorem card_barSub_ne_two {U : Subgroup G} {u : G} (w : Witness V T U u) {g : G}
    (hAT : conjSubgroup V g ≤ T) (hAQ : ¬ conjSubgroup V g ≤ pCoreOf 2 N) :
    Nat.card (barSub π (conjSubgroup V g)) ≠ 2 := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h, rfl⟩ := w.conj
  set A := conjSubgroup V g with hAdef
  set Q := pCoreOf 2 N with hQdef
  have hAN : A ≤ N := hAT.trans c.TN
  have hAel : IsElemAbelian 2 A := isElemAbelian_conjSubgroup' c.elem g
  have hAV : A ≠ V := fun h => hAQ (h ▸ c.V_le_Q)
  have hAM : A ≤ normalizer (V : Set G) := hAT.trans c.T_le_M
  have hUM : conjSubgroup V h ≤ normalizer (V : Set G) := w.le_T.trans c.T_le_M
  have huN : u ∈ N := c.TN (w.le_T w.mem)
  obtain ⟨a₁, ha₁A, ha₁Q⟩ := Set.not_subset.1 hAQ
  have ha₁N : a₁ ∈ N := hAN ha₁A
  have ha₁2 : orderOf (π ⟨a₁, ha₁N⟩) = 2 := by
    apply orderOf_eq_prime
    · have : (⟨a₁, ha₁N⟩ : ↥N) ^ 2 = 1 := Subtype.ext (hAel.2 a₁ ha₁A)
      rw [← map_pow, this, map_one]
    · intro h1
      exact ha₁Q ((c.ker _).1 h1)
  have hrel : Q.relIndex A = 2 := by rw [← card_barSub c.ker hAN]; exact h2
  have hcardA0 : 4 ≤ Nat.card ↥(Q ⊓ A) := by
    have h1 := Subgroup.relIndex_mul_card Q A
    rw [hrel] at h1
    have h3 : Nat.card A = Nat.card V := E3.card_conjSubgroup V g
    have := c.card_V
    omega
  have hA0ne : Q ⊓ A ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcardA0
    omega
  obtain ⟨⟨a₀, ha₀QA⟩, ha₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA0ne
  have ha₀1' : a₀ ≠ 1 := fun h0 => ha₀1 (Subtype.ext h0)
  set W1Q := E3.wClos V 1 Q with hW1Q
  have hA0W : Q ⊓ A ≤ W1Q := by
    refine E3.le_wClos_of_mQuot_le c.elem g inf_le_left inf_le_right ?_ c.one_lt_rk
    show padicValNat 2 ((Q ⊓ A).relIndex A) ≤ 1
    rw [Subgroup.inf_relIndex_right, hrel, padicValNat_self]
  have hNW1Q : N ≤ normalizer (W1Q : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N).trans (E3.normalizer_le_normalizer_wClos Q)
  set Y := N ⊓ centralizer (W1Q : Set G) with hY
  have hNY : N ≤ normalizer (Y : Set G) := fun n hn =>
    mem_normalizer_inf (Subgroup.le_normalizer hn) (mem_normalizer_centralizer (hNW1Q hn))
  have hYA : Y ≤ normalizer (A : Set G) := by
    intro y hy
    refine centralizer_le_normalizer_conj c.ti g ha₀QA.2 ha₀1' ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.1 hy.2) a₀ (hA0W ha₀QA)).symm
  have hYAQ : Y ⊓ A ≤ Q := by
    have h1 : Y ⊓ A ≤ pCoreOf 2 Y :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (E1.le_normalizer_inf_of_le_normalizer hYA) (hAel.isPGroup.to_le inf_le_right)
    have h2 : pCoreOf 2 Y ≤ Q :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans inf_le_left)
        (hNY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
    exact h1.trans h2
  have hcommQ : ∀ y ∈ Y, ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ Q := by
    intro y hy a ha
    apply hYAQ
    refine ⟨?_, ?_⟩
    · have h1 : a * y⁻¹ * a⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.1 (hNY (hAN ha)) y⁻¹).1 (Y.inv_mem hy)
      have := Y.mul_mem hy h1
      simpa [mul_assoc] using this
    · have h1 : y * a * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hYA hy) a).1 ha
      exact A.mul_mem h1 (A.inv_mem ha)
  have hYQ : Y ≤ Q := by
    by_contra hYQ
    set Yb := barSub π Y with hYb
    have hYbne : Yb ≠ ⊥ := fun hb => hYQ ((barSub_eq_bot_iff c.ker inf_le_left).1 hb)
    have hAb : barSub π A ≤ centralizer (Yb : Set X) := by
      rintro _ ⟨a, ha, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      have hq : π (y * a * y⁻¹ * a⁻¹) = 1 := (c.ker _).2 (hcommQ y hy a ha)
      have e : y * a = (y * a * y⁻¹ * a⁻¹) * (a * y) := by group
      calc π y * π a = π (y * a) := (map_mul _ _ _).symm
        _ = π (y * a * y⁻¹ * a⁻¹) * π (a * y) := by rw [← map_mul, ← e]
        _ = π a * π y := by rw [hq, one_mul, map_mul]
    have hnormC : (centralizer (Yb : Set X)).Normal := by
      have : Yb.Normal := barSub_normal c.surj hNY
      exact Subgroup.normal_centralizer
    have hL : Lb ≤ centralizer (Yb : Set X) :=
      c.facts.le_of_normal _ hnormC ⟨_, hAb (mem_barSub_of_mem ha₁N ha₁A), ha₁2⟩
    have hY3 : IsPGroup 3 Yb := c.facts.cent.to_le (Subgroup.le_centralizer_iff.1 hL)
    obtain ⟨yb, hyb, hyb3⟩ := exists_orderOf_eq_of_isPGroup hY3 hYbne
    obtain ⟨y, hy, hy3⟩ := exists_orderOf_eq_of_barSub hyb hyb3
    exact c.not_orderOf_three hAM hAV hy.1 (hYA hy) hy3
  have huY : u ∈ Y := by
    refine Subgroup.mem_inf.2 ⟨huN, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.1 w.cent_W1) z (E3.wClos_mono c.Q_le_T hz)
  set C1Q := E3.cClos V 1 Q with hC1Q
  have huC1 : u ∈ C1Q := ⟨hYQ huY, huY.2⟩
  have hNC1Q : N ≤ normalizer (C1Q : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N).trans (E3.normalizer_le_normalizer_cClos Q)
  have hAC : ¬ A ≤ centralizer (C1Q : Set G) := by
    intro hle
    have hND : N ≤ normalizer ((N ⊓ centralizer (C1Q : Set G) : Subgroup G) : Set G) :=
      fun n hn => mem_normalizer_inf (Subgroup.le_normalizer hn)
        (mem_normalizer_centralizer (hNC1Q hn))
    obtain ⟨x, hxD, hx3⟩ :=
      c.exists_orderOf_three_of_normal hND (a := ⟨a₁, ha₁N⟩) ⟨ha₁N, hle ha₁A⟩ ha₁2
    have hxu : x * u = u * x := ((Subgroup.mem_centralizer_iff.1 hxD.2) u huC1).symm
    exact c.not_orderOf_three_of_commute hUM w.ne w.mem w.ne_one hxD.1 hxu hx3
  have hex : ∃ a ∈ A, ∃ cc ∈ C1Q, cc * a ≠ a * cc := by
    by_contra hcon
    apply hAC
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro cc hcc
    by_contra hne
    exact hcon ⟨a, ha, cc, hcc, hne⟩
  obtain ⟨a, haA, cc, hcc, hne⟩ := hex
  have hccA : cc ∈ normalizer (A : Set G) := by
    refine centralizer_le_normalizer_conj c.ti g ha₀QA.2 ha₀1' ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.1 hcc.2) a₀ (hA0W ha₀QA)).symm
  set x := cc * a * cc⁻¹ * a⁻¹ with hx
  have hx1 : x ≠ 1 := by
    intro hx1
    apply hne
    calc cc * a = (cc * a * cc⁻¹ * a⁻¹) * (a * cc) := by group
      _ = a * cc := by rw [← hx, hx1, one_mul]
  have hxA : x ∈ A := A.mul_mem ((Subgroup.mem_normalizer_iff.1 hccA a).1 haA) (A.inv_mem haA)
  have hxC : x ∈ C1Q := by
    have h1 : a * cc⁻¹ * a⁻¹ ∈ C1Q :=
      (Subgroup.mem_normalizer_iff.1 (hNC1Q (hAN haA)) cc⁻¹).1 (C1Q.inv_mem hcc)
    have := C1Q.mul_mem hcc h1
    simpa [hx, mul_assoc] using this
  have hxW : x ∈ W1Q := hA0W ⟨hxC.1, hxA⟩
  have hxZ : x ∈ centralizer (W1Q : Set G) := hxC.2
  obtain ⟨nb, hP, hnc⟩ := c.facts.pair _ ha₁2
  obtain ⟨n, rfl⟩ := c.surj nb
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
  have hx'W : (n : G) * x * (n : G)⁻¹ ∈ W1Q := (Subgroup.mem_normalizer_iff.1 (hNW1Q n.2) x).1 hxW
  have hxx' : x * ((n : G) * x * (n : G)⁻¹) = ((n : G) * x * (n : G)⁻¹) * x :=
    ((Subgroup.mem_centralizer_iff.1 hxZ) _ hx'W).symm
  have hxNA' : x ∈ normalizer (A' : Set G) := by
    rw [hA'conj]
    exact centralizer_le_normalizer_conj c.ti (g * (n : G)⁻¹) (hA'conj ▸ hx'A') hx'1
      (Subgroup.mem_centralizer_singleton_iff.2 hxx')
  have hNA' : A ⊓ normalizer (A' : Set G) ≠ ⊥ := by
    intro hbot
    have hmem : x ∈ A ⊓ normalizer (A' : Set G) := ⟨hxA, hxNA'⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  have hA'N : A' ≤ N := by
    intro z hz
    have h1 : (n : G)⁻¹ * z * (n : G) ∈ N := by
      have := hAN (mem_conjSubgroup_iff.1 hz)
      simpa using this
    have := N.mul_mem (N.mul_mem n.2 h1) (N.inv_mem n.2)
    simpa [mul_assoc] using this
  have hbarA : barSub π A = Subgroup.zpowers (π ⟨a₁, ha₁N⟩) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact mem_barSub_of_mem ha₁N ha₁A
    · rw [Nat.card_zpowers, ha₁2, h2]
  have hP2 : IsPGroup 2 ↥(A ⊔ A') := by
    refine isPGroup_of_barSub c.ker (sup_le hAN hA'N) (hP.to_le ?_)
    have hsup : barSub π (A ⊔ A') = barSub π A ⊔ barSub π A' := by
      unfold barSub
      rw [Subgroup.subgroupOf_sup hAN hA'N, Subgroup.map_sup]
    rw [hsup]
    refine sup_le ?_ ?_
    · rw [hbarA, Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rintro _ ⟨z, hz, rfl⟩
      have hz' : (n⁻¹ * z * n : ↥N) ∈ A.subgroupOf N := by
        rw [Subgroup.mem_subgroupOf]
        have := mem_conjSubgroup_iff.1 hz
        simpa [mul_assoc] using this
      have hmem : π (n⁻¹ * z * n) ∈ Subgroup.zpowers (π ⟨a₁, ha₁N⟩) :=
        hbarA ▸ mem_barSub_of_mem' hz'
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      have hzk : π z = (π n * π ⟨a₁, ha₁N⟩ * (π n)⁻¹) ^ k := by
        rw [conj_zpow, hk, map_mul, map_mul, map_inv]
        group
      rw [hzk]
      exact Subgroup.zpow_mem _
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) k
  have hcomm := commute_of_isPGroup_sup c.elem c.ti ⟨g, hAdef⟩ ⟨g * (n : G)⁻¹, hA'conj⟩ hNA' hP2
  have h1 := hcomm a₁ ha₁A ((n : G) * a₁ * (n : G)⁻¹) (by
    rw [hA', mem_conjSubgroup_iff]
    simpa [mul_assoc] using ha₁A)
  apply hnc
  have h1' : (⟨a₁, ha₁N⟩ : ↥N) * (n * ⟨a₁, ha₁N⟩ * n⁻¹) =
      (n * ⟨a₁, ha₁N⟩ * n⁻¹) * ⟨a₁, ha₁N⟩ := Subtype.ext h1
  have := congrArg π h1'
  simpa only [map_mul, map_inv] using this

theorem four_le_card_barSub {U : Subgroup G} {u : G} (w : Witness V T U u) {g : G}
    (hAT : conjSubgroup V g ≤ T) (hAQ : ¬ conjSubgroup V g ≤ pCoreOf 2 N) :
    4 ≤ Nat.card (barSub π (conjSubgroup V g)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := c.card_barSub_ne_two w hAT hAQ
  have h1 : Nat.card (barSub π (conjSubgroup V g)) ≠ 1 := by
    rw [Ne, Subgroup.card_eq_one, barSub_eq_bot_iff c.ker (hAT.trans c.TN)]
    exact hAQ
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1
    (isPGroup_barSub (π := π) (isElemAbelian_conjSubgroup' c.elem g).isPGroup)
  rw [hk] at h1 h2 ⊢
  rcases k with _ | _ | k
  · simp at h1
  · simp at h2
  · calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Ctx

end CFSG.LocalAnalysis.WeakClosure81.NFW
