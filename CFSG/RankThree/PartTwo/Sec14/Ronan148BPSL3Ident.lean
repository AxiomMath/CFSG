module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3IdentDefs
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3Top
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3A7
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec13
open CFSG.RankThree.PartTwo.Sec4 (ModThree qSubPi PiField slPi)
open scoped commutatorElement

theorem hessGen_or_cent
    {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi X p e) (hperf : Group.IsPerfect X)
    {E : Subgroup X} (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁) :
    sSup {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ E ≤ Subgroup.normalizer (Y : Set X)} = ⊤ ∨
      ∀ x ∈ E, x ≠ 1 → IsPGroup 3 (Subgroup.centralizer ({x} : Set X)) := by
  by_cases hmod : p ^ e % 9 = 1 ∨ p ^ e % 9 = 8
  · by_cases hU38 : Sec4.IsoLThreePi X 2 3
    · right
      intro x hx hx1
      refine isPGroup_centralizer_hessian (by norm_num) hU38 (k := 2) (fun π hq => ?_) hEe hE9 htr
        hx hx1
      cases π
      · rfl
      · exact absurd hq (by norm_num [ModThree])
    · left
      exact ks142L3HessGenNine_of_model ks142L3HessGenNineModel_proof X p e he hiso hperf hmod
        hU38 E hEe hE9 htr
  · by_cases hL4 : Sec4.IsoLThreePi X 2 2
    · right
      intro x hx hx1
      refine isPGroup_centralizer_hessian (by norm_num) hL4 (k := 1) (fun π hq => ?_) hEe hE9 htr
        hx hx1
      cases π
      · exact absurd hq (by norm_num [ModThree])
      · rfl
    · left
      have h := Sec15.ks1517Gen_of (Sec15.ks1517CentGen_of ks1517SeitzU) X p e he hiso hperf hmod
        hL4 E hEe hE9
      rwa [Res6GenL3.invariantPiSubgroups_top_piCompl_eq] at h

section Facts

variable {X : Type} [Group X] [Finite X]

def restrictAut (σ : MulAut X) {K₀ : Subgroup X} (h : ∀ k ∈ K₀, σ k ∈ K₀)
    (h' : ∀ k ∈ K₀, σ⁻¹ k ∈ K₀) : MulAut ↥K₀ where
  toFun z := ⟨σ z, h z z.2⟩
  invFun z := ⟨σ⁻¹ z, h' z z.2⟩
  left_inv z := Subtype.ext (MulAut.inv_apply_self _ σ (z : X))
  right_inv z := Subtype.ext (MulAut.apply_inv_self _ σ (z : X))
  map_mul' x y := Subtype.ext (map_mul σ (x : X) (y : X))

theorem le_sSup_of_restrict {P : Subgroup (MulAut X)} {K₀ : Subgroup X}
    (hPK : ∀ σ ∈ P, ∀ k ∈ K₀, σ k ∈ K₀)
    (hgen : sSup {Y : Subgroup ↥K₀ | ¬ 3 ∣ Nat.card Y ∧
      ∀ τ ∈ autRestrict K₀ P, Y.map τ.toMonoidHom ≤ Y} = ⊤) :
    K₀ ≤ sSup {Y : Subgroup X | Y ≤ K₀ ∧ ¬ 3 ∣ Nat.card Y ∧ ∀ σ ∈ P, ∀ y ∈ Y, σ y ∈ Y} := by
  intro k hk
  have hk' : (⟨k, hk⟩ : ↥K₀) ∈ sSup {Y : Subgroup ↥K₀ | ¬ 3 ∣ Nat.card Y ∧
      ∀ τ ∈ autRestrict K₀ P, Y.map τ.toMonoidHom ≤ Y} := by
    rw [hgen]; exact Subgroup.mem_top _
  have hle : (sSup {Y : Subgroup ↥K₀ | ¬ 3 ∣ Nat.card Y ∧
      ∀ τ ∈ autRestrict K₀ P, Y.map τ.toMonoidHom ≤ Y}).map K₀.subtype ≤
      sSup {Y : Subgroup X | Y ≤ K₀ ∧ ¬ 3 ∣ Nat.card Y ∧ ∀ σ ∈ P, ∀ y ∈ Y, σ y ∈ Y} := by
    rw [(Subgroup.gc_map_comap _).l_sSup]
    refine iSup₂_le fun Y hY => le_sSup ⟨Subgroup.map_subtype_le Y, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective K₀.subtype_injective]; exact hY.1
    · rintro σ hσ _ ⟨y, hy, rfl⟩
      have hτ : restrictAut σ (hPK σ hσ) (hPK σ⁻¹ (P.inv_mem hσ)) ∈ autRestrict K₀ P :=
        ⟨σ, hσ, fun _ => rfl⟩
      exact ⟨_, hY.2 _ hτ ⟨y, hy, rfl⟩, rfl⟩
  exact hle ⟨⟨k, hk⟩, hk', rfl⟩

theorem le_sSup_of_inner {P : Subgroup (MulAut X)} {K₀ E : Subgroup X} (hEK : E ≤ K₀)
    (hPE : ∀ σ ∈ P, ∃ e ∈ E, ∀ k ∈ K₀, σ k = e * k * e⁻¹)
    (hgen : sSup {Y : Subgroup ↥K₀ | ¬ 3 ∣ Nat.card Y ∧
      E.subgroupOf K₀ ≤ Subgroup.normalizer (Y : Set ↥K₀)} = ⊤) :
    K₀ ≤ sSup {Y : Subgroup X | Y ≤ K₀ ∧ ¬ 3 ∣ Nat.card Y ∧ ∀ σ ∈ P, ∀ y ∈ Y, σ y ∈ Y} := by
  intro k hk
  have hk' : (⟨k, hk⟩ : ↥K₀) ∈ sSup {Y : Subgroup ↥K₀ | ¬ 3 ∣ Nat.card Y ∧
      E.subgroupOf K₀ ≤ Subgroup.normalizer (Y : Set ↥K₀)} := by
    rw [hgen]; exact Subgroup.mem_top _
  have hle : (sSup {Y : Subgroup ↥K₀ | ¬ 3 ∣ Nat.card Y ∧
      E.subgroupOf K₀ ≤ Subgroup.normalizer (Y : Set ↥K₀)}).map K₀.subtype ≤
      sSup {Y : Subgroup X | Y ≤ K₀ ∧ ¬ 3 ∣ Nat.card Y ∧ ∀ σ ∈ P, ∀ y ∈ Y, σ y ∈ Y} := by
    rw [(Subgroup.gc_map_comap _).l_sSup]
    refine iSup₂_le fun Y hY => le_sSup ⟨Subgroup.map_subtype_le Y, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective K₀.subtype_injective]; exact hY.1
    · rintro σ hσ _ ⟨y, hy, rfl⟩
      obtain ⟨e, heE, he⟩ := hPE σ hσ
      have heN := hY.2 (Subgroup.mem_subgroupOf.mpr
        (show ((⟨e, hEK heE⟩ : K₀) : X) ∈ E from heE))
      refine ⟨⟨e, hEK heE⟩ * y * ⟨e, hEK heE⟩⁻¹, (Subgroup.mem_normalizer_iff.mp heN y).mp hy, ?_⟩
      simp [he y y.2]
  exact hle ⟨⟨k, hk⟩, hk', rfl⟩

def innOn (K₀ : Subgroup X) : Subgroup (MulAut X) where
  carrier := {τ | ∃ k ∈ K₀, ∀ z ∈ K₀, τ z = k * z * k⁻¹}
  mul_mem' := by
    rintro τ₁ τ₂ ⟨k₁, hk₁, h₁⟩ ⟨k₂, hk₂, h₂⟩
    refine ⟨k₁ * k₂, K₀.mul_mem hk₁ hk₂, fun z hz => ?_⟩
    rw [MulAut.mul_apply, h₂ z hz, h₁ _ (K₀.mul_mem (K₀.mul_mem hk₂ hz) (K₀.inv_mem hk₂))]
    group
  one_mem' := ⟨1, K₀.one_mem, fun z _ => by simp⟩
  inv_mem' := by
    rintro τ ⟨k, hk, h⟩
    refine ⟨k⁻¹, K₀.inv_mem hk, fun z hz => ?_⟩
    have h1 := h (k⁻¹ * z * k) (K₀.mul_mem (K₀.mul_mem (K₀.inv_mem hk) hz) hk)
    have h2 : τ (k⁻¹ * z * k) = z := by rw [h1]; group
    calc τ⁻¹ z = τ⁻¹ (τ (k⁻¹ * z * k)) := by rw [h2]
      _ = k⁻¹ * z * k := MulAut.inv_apply_self _ τ _
      _ = k⁻¹ * z * k⁻¹⁻¹ := by rw [inv_inv]

theorem mem_of_normalizer_map_conj (hZ : Subgroup.center X = ⊥) {K₀ : Subgroup X}
    {σ : MulAut X} (hσ : σ ∈ Subgroup.normalizer
      ((K₀.map (MulAut.conj : X →* MulAut X) : Subgroup (MulAut X)) : Set (MulAut X)))
    {k : X} (hk : k ∈ K₀) : σ k ∈ K₀ := by
  have h1 : σ * MulAut.conj k * σ⁻¹ ∈ K₀.map (MulAut.conj : X →* MulAut X) :=
    (Subgroup.mem_normalizer_iff.mp hσ _).mp ⟨k, hk, rfl⟩
  rw [mulAut_mul_conj'] at h1
  obtain ⟨k', hk', hkk⟩ := h1
  rwa [← PS.conj_injective hZ hkk]

theorem inv_of_hyp (hZ : Subgroup.center X = ⊥) {P K₀ Q D : Subgroup _}
    (hh : SigGenHyp P (K₀.map (MulAut.conj : X →* MulAut X)) Q D) :
    ∀ σ ∈ P, ∀ k ∈ K₀, σ k ∈ K₀ :=
  fun _ hσ _ hk => mem_of_normalizer_map_conj hZ (hh.normK hσ) hk

theorem fix_of_mem_centralizer (hZ : Subgroup.center X = ⊥) {D : Subgroup (MulAut X)} {x : X}
    (hx : MulAut.conj x ∈ Subgroup.centralizer (D : Set (MulAut X))) {σ : MulAut X}
    (hσ : σ ∈ D) : σ x = x := by
  have h1 := Subgroup.mem_centralizer_iff.mp hx σ hσ
  apply PS.conj_injective hZ
  rw [← mulAut_mul_conj', h1, mul_inv_cancel_right]

theorem eq_one_of_trivial {P K₀ Q D : Subgroup _}
    (hh : SigGenHyp P (K₀.map (MulAut.conj : X →* MulAut X)) Q D) {σ : MulAut X} (hσ : σ ∈ P)
    (htriv : ∀ k ∈ K₀, σ k = k) : σ = 1 := by
  refine hh.faith σ hσ fun a ha => ?_
  obtain ⟨k, hk, rfl⟩ := ha
  rw [mulAut_mul_conj', htriv k hk, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem exists_not_comm {P K₀ Q D : Subgroup _}
    (hQ : Q ≤ (MulAut.conj : X →* MulAut X).range)
    (hh : SigGenHyp P (K₀.map (MulAut.conj : X →* MulAut X)) Q D) :
    ∃ x : X, MulAut.conj x ∈ Q ∧ ∃ k ∈ K₀, x * k * x⁻¹ ≠ k := by
  by_contra hcon
  push_neg at hcon
  apply hh.nontriv
  rw [Subgroup.commutator_le]
  rintro _ ⟨k, hk, rfl⟩ q hq
  obtain ⟨x, rfl⟩ := hQ hq
  have hxk := hcon x hq k hk
  have hc : x * k = k * x := by
    calc x * k = x * k * x⁻¹ * x := by group
      _ = k * x := by rw [hxk]
  have h1 : ⁅MulAut.conj k, MulAut.conj x⁆ = 1 := by
    rw [← map_commutatorElement, commutatorElement_def, ← hc]
    simp
  rw [h1]
  exact Subgroup.one_mem _

theorem exists_inv_of_hyp (hZ : Subgroup.center X = ⊥) {P K Q D : Subgroup (MulAut X)}
    (hQ : Q ≤ (MulAut.conj : X →* MulAut X).range) (hh : SigGenHyp P K Q D) :
    ∃ Y : Subgroup X, Y ≠ ⊥ ∧ ¬ 3 ∣ Nat.card Y ∧ ∀ σ ∈ P, Y.map σ.toMonoidHom ≤ Y := by
  have hinj := PS.conj_injective hZ
  have hQi := mem_invariantPiSubgroups_iff.mp hh.inv
  refine ⟨Q.comap MulAut.conj, ?_, ?_, ?_⟩
  · intro hbot
    apply hh.nontriv
    have hQb : Q = ⊥ := by rw [← Subgroup.map_comap_eq_self hQ, hbot, Subgroup.map_bot]
    rw [hQb, Subgroup.commutator_bot_right]
    exact bot_le
  · rw [card_comap_of_le_range MulAut.conj hinj hQ]
    exact (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQi.2.1
  · rintro σ hσ _ ⟨x, hx, rfl⟩
    change MulAut.conj (σ x) ∈ Q
    rw [← mulAut_mul_conj']
    exact (Subgroup.mem_normalizer_iff.mp (hQi.2.2 hσ) _).mp hx

theorem commutator_le_innOn (hZ : Subgroup.center X = ⊥) {P K₀ Q : Subgroup _}
    (hQ : Q ≤ (MulAut.conj : X →* MulAut X).range)
    (hQK : Q ≤ Subgroup.normalizer
      ((K₀.map (MulAut.conj : X →* MulAut X) : Subgroup (MulAut X)) : Set (MulAut X)))
    (hPI : P ≤ innOn K₀) : ⁅Q, P⁆ ≤ innOn K₀ := by
  rw [Subgroup.commutator_le]
  intro q hq σ hσ
  obtain ⟨x, rfl⟩ := hQ hq
  obtain ⟨e, heK, hσe⟩ := hPI hσ
  have hxinv : MulAut.conj x⁻¹ ∈ Q := by rw [map_inv]; exact Q.inv_mem hq
  have hxK' : ∀ k ∈ K₀, x⁻¹ * k * x ∈ K₀ := by
    intro k hk
    have := mem_of_normalizer_map_conj hZ (hQK hxinv) hk
    rwa [MulAut.conj_apply, inv_inv] at this
  have hxK : ∀ k ∈ K₀, x * k * x⁻¹ ∈ K₀ := by
    intro k hk
    have := mem_of_normalizer_map_conj hZ (hQK hq) hk
    rwa [MulAut.conj_apply] at this
  refine ⟨x * e * x⁻¹ * e⁻¹, K₀.mul_mem (hxK e heK) (K₀.inv_mem heK), fun z hz => ?_⟩
  have hez : e⁻¹ * z * e ∈ K₀ := K₀.mul_mem (K₀.mul_mem (K₀.inv_mem heK) hz) heK
  have hσinv : σ⁻¹ z = e⁻¹ * z * e := by
    have h1 := hσe (e⁻¹ * z * e) hez
    rw [show e * (e⁻¹ * z * e) * e⁻¹ = z by group] at h1
    calc σ⁻¹ z = σ⁻¹ (σ (e⁻¹ * z * e)) := by rw [h1]
      _ = e⁻¹ * z * e := MulAut.inv_apply_self _ σ _
  have hw : x⁻¹ * (e⁻¹ * z * e) * x ∈ K₀ := hxK' _ hez
  rw [commutatorElement_def, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hσinv,
    MulAut.conj_inv_apply, hσe _ hw, MulAut.conj_apply]
  group

theorem false_of_inner_cent (hZ : Subgroup.center X = ⊥) {P K₀ Q D : Subgroup _}
    (hP9 : Nat.card P = 9) (hQ : Q ≤ (MulAut.conj : X →* MulAut X).range)
    (hh : SigGenHyp P (K₀.map (MulAut.conj : X →* MulAut X)) Q D)
    (hZ₀ : Subgroup.center ↥K₀ = ⊥) {E : Subgroup X} (hEK : E ≤ K₀)
    (hcent : ∀ e ∈ E, e ≠ 1 → IsPGroup 3 ↥(K₀ ⊓ Subgroup.centralizer ({e} : Set X)))
    (hPE : ∀ σ ∈ P, ∃ e ∈ E, ∀ k ∈ K₀, σ k = e * k * e⁻¹) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := PS.conj_injective hZ
  obtain ⟨hDP, hcard⟩ := hh.hyp
  have hDne : D ≠ ⊥ := by
    intro hD
    rw [hD, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨σd, hσdD⟩, hσd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have hσd1' : σd ≠ 1 := fun h => hσd1 (Subtype.ext h)
  obtain ⟨ed, hedE, hσde⟩ := hPE σd (hDP hσdD)
  have hed1 : ed ≠ 1 := by
    intro h
    apply hσd1'
    refine eq_one_of_trivial hh (hDP hσdD) fun k hk => ?_
    rw [hσde k hk, h]
    group
  have hedK := hEK hedE
  have hF := hcent ed hedE hed1
  have hPI : P ≤ innOn K₀ := fun σ hσ => by
    obtain ⟨e, he, h⟩ := hPE σ hσ
    exact ⟨e, hEK he, h⟩
  have hQI : Q ≤ innOn K₀ := le_of_eq_of_le hh.comm (commutator_le_innOn hZ hQ hh.normQ hPI)
  have h3Q : ¬ 3 ∣ Nat.card Q :=
    (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp (mem_invariantPiSubgroups_iff.mp hh.inv).2.1
  have hcentK : ∀ x : X, MulAut.conj x ∈ Q → ∀ z ∈ K₀, x * z * x⁻¹ = z := by
    intro x hx
    obtain ⟨k, hkK, hk⟩ := hQI hx
    have hk' : ∀ z ∈ K₀, x * z * x⁻¹ = k * z * k⁻¹ := fun z hz => by
      rw [← hk z hz, MulAut.conj_apply]
    have hfix : σd x = x := fix_of_mem_centralizer hZ (hh.cent hx) hσdD
    have hstar : ∀ w ∈ K₀, (ed * k) * w * (ed * k)⁻¹ = (k * ed) * w * (k * ed)⁻¹ := by
      intro w hw
      have hew : ed * w * ed⁻¹ ∈ K₀ := K₀.mul_mem (K₀.mul_mem hedK hw) (K₀.inv_mem hedK)
      have hkw : k * w * k⁻¹ ∈ K₀ := K₀.mul_mem (K₀.mul_mem hkK hw) (K₀.inv_mem hkK)
      have hA : σd (x * w * x⁻¹) = k * (ed * w * ed⁻¹) * k⁻¹ := by
        rw [map_mul, map_mul, map_inv, hfix, hσde w hw, hk' _ hew]
      have hB : σd (x * w * x⁻¹) = ed * (k * w * k⁻¹) * ed⁻¹ := by
        rw [hk' w hw, hσde _ hkw]
      calc (ed * k) * w * (ed * k)⁻¹ = ed * (k * w * k⁻¹) * ed⁻¹ := by group
        _ = k * (ed * w * ed⁻¹) * k⁻¹ := by rw [← hB, hA]
        _ = (k * ed) * w * (k * ed)⁻¹ := by group
    have hgK : k⁻¹ * ed⁻¹ * k * ed ∈ K₀ :=
      K₀.mul_mem (K₀.mul_mem (K₀.mul_mem (K₀.inv_mem hkK) (K₀.inv_mem hedK)) hkK) hedK
    have hg : (⟨k⁻¹ * ed⁻¹ * k * ed, hgK⟩ : ↥K₀) ∈ Subgroup.center ↥K₀ := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      change (w : X) * (k⁻¹ * ed⁻¹ * k * ed) = k⁻¹ * ed⁻¹ * k * ed * w
      calc (w : X) * (k⁻¹ * ed⁻¹ * k * ed)
          = (k⁻¹ * ed⁻¹) * ((ed * k) * w * (ed * k)⁻¹) * (k * ed) := by group
        _ = (k⁻¹ * ed⁻¹) * ((k * ed) * w * (k * ed)⁻¹) * (k * ed) := by rw [hstar w w.2]
        _ = k⁻¹ * ed⁻¹ * k * ed * w := by group
    rw [hZ₀, Subgroup.mem_bot] at hg
    have hg1 : k⁻¹ * ed⁻¹ * k * ed = 1 := congrArg Subtype.val hg
    have hkC : k ∈ Subgroup.centralizer ({ed} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc k * ed = ed * k * (k⁻¹ * ed⁻¹ * k * ed) := by group
        _ = ed * k := by rw [hg1, mul_one]
    have hpow : ∀ m : ℕ, ∀ z ∈ K₀, x ^ m * z * (x ^ m)⁻¹ = k ^ m * z * (k ^ m)⁻¹ := by
      intro m
      induction m with
      | zero => intro z _; simp
      | succ m ih =>
        intro z hz
        have hzm : k ^ m * z * (k ^ m)⁻¹ ∈ K₀ :=
          K₀.mul_mem (K₀.mul_mem (K₀.pow_mem hkK m) hz) (K₀.inv_mem (K₀.pow_mem hkK m))
        calc x ^ (m + 1) * z * (x ^ (m + 1))⁻¹ = x * (x ^ m * z * (x ^ m)⁻¹) * x⁻¹ := by
              rw [pow_succ']; group
          _ = x * (k ^ m * z * (k ^ m)⁻¹) * x⁻¹ := by rw [ih z hz]
          _ = k * (k ^ m * z * (k ^ m)⁻¹) * k⁻¹ := hk' _ hzm
          _ = k ^ (m + 1) * z * (k ^ (m + 1))⁻¹ := by rw [pow_succ']; group
    set n := orderOf x with hn
    have hkn : k ^ n = 1 := by
      have hc : (⟨k ^ n, K₀.pow_mem hkK n⟩ : ↥K₀) ∈ Subgroup.center ↥K₀ := by
        rw [Subgroup.mem_center_iff]
        intro w
        apply Subtype.ext
        change (w : X) * k ^ n = k ^ n * w
        have h1 := hpow n w w.2
        rw [hn, pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
        calc (w : X) * k ^ n = (k ^ n * w * (k ^ n)⁻¹) * k ^ n := by rw [← h1]
          _ = k ^ n * w := by group
      rw [hZ₀, Subgroup.mem_bot] at hc
      exact congrArg Subtype.val hc
    have hn3 : ¬ 3 ∣ n := by
      intro h3
      apply h3Q
      refine h3.trans ?_
      rw [hn, ← orderOf_injective MulAut.conj hinj x]
      exact Subgroup.orderOf_dvd_natCard Q hx
    obtain ⟨j, hj⟩ := hF ⟨k, hkK, hkC⟩
    have hkj : k ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hcop : Nat.Coprime (3 ^ j) n :=
      Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn3)
    have hk1 : orderOf k = 1 := Nat.dvd_one.mp (by
      rw [← Nat.Coprime.gcd_eq_one hcop]
      exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hkj) (orderOf_dvd_of_pow_eq_one hkn))
    rw [orderOf_eq_one_iff] at hk1
    intro z hz
    rw [hk' z hz, hk1]
    group
  obtain ⟨x, hx, k, hk, hxk⟩ := exists_not_comm hQ hh
  exact hxk (hcentK x hx k hk)

theorem sigGenConcl_of_hess
    (hZ : Subgroup.center X = ⊥) {P : Subgroup (MulAut X)} (hP : IsPGroup 3 P)
    (hP9 : Nat.card P = 9) {F : Subgroup X} (hF3 : IsPGroup 3 F)
    (hF : ∀ x : X, (∀ σ ∈ P, σ x = x) → x ∈ F) {K₀ : Subgroup X} {Q D : Subgroup (MulAut X)}
    (hQ : Q ≤ (MulAut.conj : X →* MulAut X).range)
    (hh : SigGenHyp P (K₀.map (MulAut.conj : X →* MulAut X)) Q D)
    (hK₀p : Group.IsPerfect ↥K₀) (hL₀ : IsLThreePi ↥K₀) {E : Subgroup X} (hEK : E ≤ K₀)
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ K₀, w ∈ Subgroup.normalizer (E : Set X) ∧ w * y₀ * w⁻¹ = y₁)
    (hPE : ∀ σ ∈ P, ∃ e ∈ E, ∀ k ∈ K₀, σ k = e * k * e⁻¹) :
    SigGenConcl P (K₀.map (MulAut.conj : X →* MulAut X)) := by
  have hinj := PS.conj_injective hZ
  obtain ⟨p, f, hp, hf, hiso⟩ := hL₀
  set E' := E.subgroupOf K₀ with hE'
  have hEe' : CFSG.Assembly.IsElemAbelian 3 E' :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_subgroupOf 3 E K₀ hEe
  have hE9' : Nat.card E' = 9 := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hE9]
  have htr' : ∀ y₀ ∈ E', y₀ ≠ 1 → ∀ y₁ ∈ E', y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E' : Set ↥K₀), w * y₀ * w⁻¹ = y₁ := by
    intro y₀ hy₀ hy₀1 y₁ hy₁ hy₁1
    have h0 : (y₀ : X) ≠ 1 := fun h => hy₀1 (Subtype.ext h)
    have h1 : (y₁ : X) ≠ 1 := fun h => hy₁1 (Subtype.ext h)
    obtain ⟨w, hwK, hwN, hw⟩ :=
      htr y₀ (Subgroup.mem_subgroupOf.mp hy₀) h0 y₁ (Subgroup.mem_subgroupOf.mp hy₁) h1
    refine ⟨⟨w, hwK⟩, ?_, Subtype.ext hw⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hwN (z : X)
  rcases hessGen_or_cent hf hiso hK₀p hEe' hE9' htr' with hgen | hc
  · exact sigGenConcl_of_gen hZ hP hF3 hF (le_sSup_of_inner hEK hPE hgen)
  · exfalso
    have h3K : 3 ∣ Nat.card K₀ := by
      rw [← Subgroup.card_map_of_injective hinj]; exact hh.three
    have : Nontrivial ↥K₀ := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      rw [Nat.card_of_subsingleton (1 : ↥K₀)] at h3K
      omega
    have hZ₀ : Subgroup.center ↥K₀ = ⊥ := center_eq_bot_of_isLThreePi ⟨p, f, hp, hf, hiso⟩ hK₀p
    refine false_of_inner_cent hZ hP9 hQ hh hZ₀ hEK (fun e he he1 => ?_) hPE
    have he' : (⟨e, hEK he⟩ : ↥K₀) ∈ E' := Subgroup.mem_subgroupOf.mpr he
    have he1' : (⟨e, hEK he⟩ : ↥K₀) ≠ 1 := fun h => he1 (congrArg Subtype.val h)
    have hC := hc _ he' he1'
    let φ : ↥(K₀ ⊓ Subgroup.centralizer ({e} : Set X)) →*
        ↥(Subgroup.centralizer ({(⟨e, hEK he⟩ : ↥K₀)} : Set ↥K₀)) :=
      { toFun := fun g => ⟨⟨g, g.2.1⟩, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine hC.of_injective φ fun a b hab => ?_
    have hab' := congrArg (fun t : ↥(Subgroup.centralizer ({(⟨e, hEK he⟩ : ↥K₀)} : Set ↥K₀)) =>
      ((t : ↥K₀) : X)) hab
    exact Subtype.ext hab'

end Facts

theorem kf148SigGenL3_of_ident
    (h : KF148SigGenL3Ident) : KF148SigGenL3 := by
  intro Γ _ _ A L b hA hbA hb1 hLb hAL hsec hAF h131 hL h46 hpt hns
  rw [sigGen148_iff]
  intro K Q D hK hQ hh
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hperf, hZ⟩ := isPerfect_center_of_isLThreePi hL hns
  have hinj := PS.conj_injective hZ
  obtain ⟨hPe, hP9⟩ := autThetaQuot_e9 hA hbA hb1 hAL hsec
  have hP : IsPGroup 3 (Sec4.autThetaQuot A L) := fun g =>
    ⟨1, Subtype.ext (by simpa using hPe.2 g g.2)⟩
  have hfix := hpt.2.1
  obtain ⟨K₀, rfl⟩ : ∃ K₀ : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L),
      K = K₀.map (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut _) :=
    ⟨K.comap MulAut.conj, (Subgroup.map_comap_eq_self hK).symm⟩
  by_cases htop : K₀ = ⊤
  · subst htop
    rw [← MonoidHom.range_eq_map]
    exact sigGenConcl_top_of_pointFacts hA hbA hb1 hLb hAL hsec hL hns hpt
      (exists_inv_of_hyp hZ hQ hh)
  ·
    set eK := K₀.equivMapOfInjective _ hinj with heK
    have hK₀p : Group.IsPerfect ↥K₀ := by
      haveI := hh.perf
      exact Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
    have hθ := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eK
    have hK₀q : IsQuasisimple (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.congr _ _ eK hθ).symm hh.quasi
    rcases h Γ A L b hA hbA hb1 hLb hAL hsec hAF h131 hL h46 hpt hns K₀ Q D hQ hh htop hK₀p hK₀q
        (hpt.2.2.2.1 K₀ hK₀p hK₀q) with
      ⟨hL₀, E, hEK, hEe, hE9, htr, hPE⟩ | hM | ⟨⟨φ⟩, E, hEK, hE9, hPE⟩ | ⟨hZ₀, E, hEK, hcent, hPE⟩
    · exact sigGenConcl_of_hess hZ hP hP9 hfix (fun x hx => hx) hQ hh hK₀p hL₀ hEK hEe hE9 htr
        hPE
    · exact sigGenConcl_of_gen hZ hP hfix (fun x hx => hx)
        (le_sSup_of_restrict (inv_of_hyp hZ hh) (gen_of_pglModel hM hK₀p))
    · exact sigGenConcl_of_alt7 hZ hP hfix (fun x hx => hx) φ hEK hE9 hPE
    · exact (false_of_inner_cent hZ hP9 hQ hh hZ₀ hEK hcent hPE).elim

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
