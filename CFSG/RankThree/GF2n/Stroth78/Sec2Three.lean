module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Defs
public import CFSG.RankThree.GF2n.Stroth78.Sec2Orthogonality

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem sq_eq_one_of_isConj (S : Setting z E F) {a : G} (ha : IsConj z a) : a ^ 2 = 1 := by
  have hz2 : z ^ 2 = 1 := by
    rw [← S.hyp.orderOf_z]
    exact pow_orderOf_eq_one z
  have h := ha.pow 2
  rw [hz2] at h
  exact isConj_one_right.mp h

theorem mem_QaOf_self (a : G) : a ∈ QaOf a := by
  refine fStar_cent (Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)) (fun q hq => ?_)
  · rw [Set.mem_singleton_iff] at hy
    subst y
    rfl
  · exact Subgroup.mem_centralizer_iff.mp (fStar_le (Subgroup.centralizer ({a} : Set G)) hq)
      a (Set.mem_singleton a)

theorem centralizer_centralizer_CQ_eq (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (haZ : a ∉ ZQ z) (ha2 : a ^ 2 = 1) :
    Subgroup.centralizer (Subgroup.centralizer ({a} : Set G) ⊓ Q z : Set G) ⊓ Q z =
      Subgroup.zpowers a ⊔ ZQ z := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) ⊓ Q z with hC
  change Subgroup.centralizer (C : Set G) ⊓ Q z = Subgroup.zpowers a ⊔ ZQ z
  have hCQ : C ≤ Q z := by rw [hC]; exact inf_le_right
  have hZC : ZQ z ≤ C := by
    rw [hC]
    intro x hx
    obtain ⟨hxQ, hxcent⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hxcent a haQ), hxQ⟩
  have hle : Subgroup.zpowers a ⊔ ZQ z ≤ Subgroup.centralizer (C : Set G) ⊓ Q z := by
    refine sup_le ?_ ?_
    · intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr (fun c hc => ?_),
        Subgroup.zpow_mem (Q z) haQ k⟩
      have hc' : c ∈ Subgroup.centralizer ({a} : Set G) := (Subgroup.mem_inf.mp hc).1
      have hca : a * c = c * a := Subgroup.mem_centralizer_iff.mp hc' a (Set.mem_singleton a)
      exact (Commute.zpow_left hca k).eq.symm
    · intro y hy
      obtain ⟨hyQ, hycent⟩ := Subgroup.mem_inf.mp hy
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr (fun c hc => ?_), hyQ⟩
      exact hycent c (Subgroup.mem_inf.mp hc).2
  obtain ⟨e, he, f, hf, haef, -, hfZ⟩ := decomp_involution S haQ haZ ha2
  have hcardC : Nat.card C = Nat.card E * (Nat.card F / 2) :=
    card_centralizer_Q S haQ haZ ha2 ⟨e, he, haef⟩ hf hfZ
  have hEvenF : Even (Nat.card F) := by
    obtain ⟨n, hn⟩ := S.hyp.extraspecial.1.exists_card_eq
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exfalso
        rw [h, pow_zero] at hn
        have h2 : Nat.card (⁅F, F⁆ : Subgroup G) = 2 := S.hyp.extraspecial.2.2
        have hle' : Nat.card (⁅F, F⁆ : Subgroup G) ≤ Nat.card F :=
          Subgroup.card_le_of_le (Subgroup.commutator_le_self F)
        omega
      · exact h
    exact ⟨2 ^ (n - 1), by
      rw [hn, show 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) by
        rw [← two_mul, ← pow_succ']
        congr 1
        omega]⟩
  have h2F : 2 * (Nat.card F / 2) = Nat.card F := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hEvenF.two_dvd
  have h2C : 2 * Nat.card C = Nat.card (Q z) := by
    rw [hcardC, Q_card S, ← Nat.mul_assoc, Nat.mul_comm 2 (Nat.card E), Nat.mul_assoc, h2F]
  have horthC := commutatorOrthogonality S C hZC hCQ
  have hkey : Nat.card ↥(Subgroup.centralizer (C : Set G) ⊓ Q z) * Nat.card C =
      (2 * Nat.card (ZQ z)) * Nat.card C := by
    rw [horthC, ← h2C]
    ring
  have hcard : Nat.card ↥(Subgroup.centralizer (C : Set G) ⊓ Q z) = 2 * Nat.card (ZQ z) :=
    Nat.mul_right_cancel (Nat.card_pos (α := C)) hkey
  have ha1 : a ≠ 1 := by
    intro h
    exact haZ (h ▸ one_mem (ZQ z))
  have hord : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hcardzp : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers, hord]
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ ZQ z, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hycent : y ∈ Subgroup.centralizer (Q z : Set G) := (Subgroup.mem_inf.mp hy).2
    exact (Commute.zpow_left (hycent a haQ) k).eq
  have hinf : Subgroup.zpowers a ⊓ ZQ z = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro w hw
    rw [Subgroup.mem_bot]
    obtain ⟨hwz, hwZ⟩ := Subgroup.mem_inf.mp hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwz
    rw [← hk]
    have ha2z : a ^ (2 : ℤ) = 1 := by simpa [zpow_two, pow_two] using ha2
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [zpow_mul, ha2z]
      simp
    · exfalso
      apply haZ
      rw [← hk, zpow_add, zpow_mul] at hwZ
      simpa [ha2z] using hwZ
  have hcardSup : Nat.card ↥(Subgroup.zpowers a ⊔ ZQ z) = 2 * Nat.card (ZQ z) := by
    rw [card_sup_of_comm hcomm hinf, hcardzp]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcardSup])).symm

theorem exists_conj_eq_mul_z_of_mem_Q (S : Setting z E F) {a b : G}
    (haQ : a ∈ Q z) (hbQ : b ∈ Q z) (hb : b ∉ Subgroup.zpowers a ⊔ ZQ z) :
    ∃ c : G, c ∈ Q z ∧ c ∈ Subgroup.centralizer ({a} : Set G) ∧ c * b * c⁻¹ = b * z := by
  classical
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  let V := Additive (QbarOf S)
  let B : LinearMap.BilinForm (ZMod 2) V := (q S).polarBilin
  let aV : V := Additive.ofMul (QuotientGroup.mk (⟨a, haQ⟩ : ↥(Q z)))
  let bV : V := Additive.ofMul (QuotientGroup.mk (⟨b, hbQ⟩ : ↥(Q z)))
  haveI : Finite V := inferInstance
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hB : B.Nondegenerate := by
    dsimp only [B]
    exact q_nondegenerate S
  have hBsymm : B.IsSymm := by
    refine ⟨fun x y => ?_⟩
    simp only [B, QuadraticMap.polarBilin_apply_apply]
    exact QuadraticMap.polar_comm (q S) x y
  have hBrefl : B.IsRefl := hBsymm.isRefl
  let W : Submodule (ZMod 2) V := Submodule.span (ZMod 2) ({aV} : Set V)
  have hWorth : B.orthogonal (B.orthogonal W) = W :=
    LinearMap.BilinForm.orthogonal_orthogonal hB hBrefl W
  have hbspan : bV ∉ W := by
    intro hspan
    apply hb
    change bV ∈ Submodule.span (ZMod 2) ({aV} : Set V) at hspan
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hspan
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases k with rfl | rfl
    · have hb0 : (QuotientGroup.mk (⟨b, hbQ⟩ : ↥(Q z)) : QbarOf S) = 1 := by
        have h' : bV = (0 : V) := by
          rw [← hk]
          simp
        simpa [bV] using congrArg Additive.toMul h'
      have hbZ : b ∈ ZQ z := by
        have hmem : (⟨b, hbQ⟩ : ↥(Q z)) ∈ (ZQ z).subgroupOf (Q z) :=
          (QuotientGroup.eq_one_iff _).mp hb0
        exact Subgroup.mem_subgroupOf.mp hmem
      exact Subgroup.mem_sup_right hbZ
    · have hb1 : (QuotientGroup.mk (⟨b, hbQ⟩ : ↥(Q z)) : QbarOf S) =
          QuotientGroup.mk (⟨a, haQ⟩ : ↥(Q z)) := by
        have h' : bV = aV := by
          rw [← hk]
          simp
        simpa [bV, aV] using congrArg Additive.toMul h'
      have hmul : (QuotientGroup.mk ((⟨b, hbQ⟩ : ↥(Q z)) * (⟨a, haQ⟩ : ↥(Q z))⁻¹) :
          QbarOf S) = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hb1, mul_inv_cancel]
      have hmem : (⟨b, hbQ⟩ : ↥(Q z)) * (⟨a, haQ⟩ : ↥(Q z))⁻¹ ∈
          (ZQ z).subgroupOf (Q z) :=
        (QuotientGroup.eq_one_iff _).mp hmul
      have hmemG : b * a⁻¹ ∈ ZQ z := by
        have hh := Subgroup.mem_subgroupOf.mp hmem
        simpa using hh
      have hb_eq : b = (b * a⁻¹) * a := by group
      rw [hb_eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hmemG)
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  have hex : ∃ cV : V, cV ∈ B.orthogonal W ∧ B cV bV ≠ 0 := by
    by_contra h
    push Not at h
    have hborth : bV ∈ B.orthogonal (B.orthogonal W) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro x hx
      exact h x hx
    rw [hWorth] at hborth
    exact hbspan hborth
  obtain ⟨cV, hcW, hcb⟩ := hex
  have hc1 : B cV bV = 1 := by
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases (B cV bV) with h | h
    · exact absurd h hcb
    · exact h
  obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective ((ZQ z).subgroupOf (Q z)) (Additive.toMul cV)
  rw [QuotientGroup.mk'_apply] at hc
  have hcV : Additive.ofMul (QuotientGroup.mk c) = cV := by
    simpa using congrArg Additive.ofMul hc
  let cG : G := c
  have horth_a : B aV cV = 0 :=
    LinearMap.BilinForm.mem_orthogonal_iff.mp hcW aV (Submodule.mem_span_singleton_self aV)
  have hpolar_a : QuadraticMap.polar (q S) (QuotientGroup.mk (⟨a, haQ⟩ : ↥(Q z)))
      (QuotientGroup.mk c) = 0 := by
    have h := horth_a
    rw [← hcV] at h
    exact h
  have hcomm_ac : a * cG = cG * a :=
    (polar_q_eq_zero_iff S (⟨a, haQ⟩ : ↥(Q z)) c).mp hpolar_a
  have hca : cG ∈ Subgroup.centralizer ({a} : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact hcomm_ac
  have hcb1 : QuadraticMap.polar (q S) (QuotientGroup.mk c)
      (QuotientGroup.mk (⟨b, hbQ⟩ : ↥(Q z))) = 1 := by
    have h := hc1
    rw [← hcV] at h
    exact h
  have hcb_ne : ⁅cG, b⁆ ≠ 1 := by
    intro h
    have hcomm : cG * b = b * cG := commutatorElement_eq_one_iff_mul_comm.mp h
    have h0 : QuadraticMap.polar (q S) (QuotientGroup.mk c)
        (QuotientGroup.mk (⟨b, hbQ⟩ : ↥(Q z))) = 0 :=
      (polar_q_eq_zero_iff S c (⟨b, hbQ⟩ : ↥(Q z))).mpr hcomm
    rw [hcb1] at h0
    exact one_ne_zero h0
  have hderiv : ⁅cG, b⁆ ∈ Subgroup.zpowers z := by
    have h1 : ⁅cG, b⁆ ∈ ⁅Q z, Q z⁆ := Subgroup.commutator_mem_commutator c.2 hbQ
    rwa [Q_deriv_eq S] at h1
  have hz2 : z ^ 2 = 1 := by
    rw [← S.hyp.orderOf_z]
    exact pow_orderOf_eq_one z
  have hz_eq : ⁅cG, b⁆ = z := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hderiv
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · exfalso
      apply hcb_ne
      rw [← hk, zpow_mul]
      simp [hz2]
    · rw [← hk, zpow_add, zpow_mul]
      simp [hz2]
  have hzb : z * b = b * z := by
    have hzcent : z ∈ Subgroup.centralizer (Q z : Set G) :=
      (Subgroup.mem_inf.mp (z_mem_ZQ S)).2
    exact (hzcent b hbQ).symm
  refine ⟨cG, c.2, hca, ?_⟩
  calc
    cG * b * cG⁻¹ = ⁅cG, b⁆ * b := by rw [commutatorElement_def]; group
    _ = z * b := by rw [hz_eq]
    _ = b * z := hzb

end CFSG.RankThree.GF2n.Stroth78
