module

public import CFSG.Quasithin.Recognition.St84.Sec5Step11
public import CFSG.Quasithin.Recognition.F112J2Ext
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy
public import CFSG.Quasithin.Recognition.St84.Sec6S5
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.Quasithin.Background.GoldschmidtAmalgamNBasic
import CFSG.Monster.AxisCount.Abstract
import CFSG.Quasithin.Recognition.HSTypeK

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup

theorem caseC_n (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) : n₀ = 2 ∧ Nat.card Y.S = 2 ^ 7 ∧ Y.VNbr0 = Y.Q 0 ∧ Y.Q 0 ⊓ Y.Q 2 = Y.Z 1 := by
  have hr : Y.IsMaxRegLen 6 := isMaxRegLen_six Y H hZ
  have hc : Y.J2Arc := j2Arc_of_five Y H hZ h5
  have hS : Nat.card Y.S = 8 * 2 ^ (2 * n₀) :=
    card_S_of_isMaxRegLen_six_J2Arc Y H hr hc h5
  obtain ⟨hn0, hV⟩ := n_eq_two_of_card_S Y H hZ hS
  have hScard : Nat.card Y.S = 2 ^ 7 := by
    rw [hS, hn0]
    norm_num
  have hQ1leE : Y.Q 1 ≤ Y.edgeSylow 1 := Y.Q_le_edgeSylow_left 1
  have hedge : Nat.card (Y.edgeSylow 1) = 2 ^ 7 := by
    rw [Y.card_edgeSylow_eq 1, Y.edgeSylow_zero]
    exact hScard
  have hcardQ1 : Nat.card ↥(Y.Q 1) = 2 ^ 6 := by
    have h := Subgroup.relIndex_mul_card (H := Y.Q 1) (K := Y.edgeSylow 1)
    rw [inf_eq_left.mpr hQ1leE, Y.relIndex_Q_edgeSylow 1, H.n_one, hedge] at h
    omega
  obtain ⟨d, hdJ, hd3⟩ := exists_J_three Y H
  have hdL : d ∈ Y.L 1 :=
    Y.J_le_L 1 hdJ
  have hAexp := s52_A_eq Y H hZ hdL hd3
  have hAeq : Y.Q 0 ⊓ Y.Q 2 =
      Y.Q 0 ⊓ Y.Q 2 ⊓ Subgroup.centralizer ({d} : Set G) ⊔ Y.Z 1 := hAexp.1
  have hAleQ1 : Y.Q 0 ⊓ Y.Q 2 ≤ Y.Q 1 := by
    simpa using (Y.shift 1).Q_neg_one_inf_Q_one_le_Q_zero
  have hn2' : Y.n 2 = 2 := by rw [Y.n_two, H.n_zero, hn0]
  have hArel := Y.relIndex_inf_Q H 1
  rw [show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num, hn2'] at hArel
  have hAcard : Nat.card ↥(Y.Q 0 ⊓ Y.Q 2) = 4 := by
    have h := Subgroup.relIndex_mul_card (H := Y.Q 0 ⊓ Y.Q 2) (K := Y.Q 1)
    rw [inf_eq_left.mpr hAleQ1, hArel, hcardQ1] at h
    omega
  have hZ1A : Y.Z 1 ≤ Y.Q 0 ⊓ Y.Q 2 := by
    rw [hAeq]
    exact le_sup_right
  have hZ1card : Nat.card ↥(Y.Z 1) = 4 := (s52_step8_Z Y H hZ 1 (by norm_num)).2
  haveI : Finite ↥(Y.Q 0) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 0)
  haveI : Finite ↥(Y.Q 0 ⊓ Y.Q 2) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hAZ : Y.Q 0 ⊓ Y.Q 2 = Y.Z 1 :=
    (Subgroup.eq_of_le_of_card_ge hZ1A (by rw [hAcard, hZ1card])).symm
  exact ⟨hn0, hScard, hV, hAZ⟩

private noncomputable def xOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (u : Γ.neighborSet (Y.vert 0)) : G :=
  Classical.choose (exists_mem_vertZ_not_mem_Z_zero Y H hZ u)

private theorem xOf_spec (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (u : Γ.neighborSet (Y.vert 0)) :
    xOf Y H hZ u ∈ vertZ (G := G) (u : V) ∧ xOf Y H hZ u ∉ Y.Z 0 :=
  Classical.choose_spec (exists_mem_vertZ_not_mem_Z_zero Y H hZ u)

private theorem L_zero_two_trans (Y : Setup Γ G) (hn0 : Y.n 0 = 2)
    {u v u' v' : Γ.neighborSet (Y.vert 0)} (huv : u ≠ v) (hu'v' : u' ≠ v') :
    ∃ g ∈ Y.L 0, g • (u : V) = (u' : V) ∧ g • (v : V) = (v' : V) := by
  let e := Y.nbrEquiv 0 hn0
  let Hsub : Subgroup ↥(Y.Gi 0) := (Y.L 0).subgroupOf (Y.Gi 0)
  have hmap : Hsub.map (Y.nbrRep 0 hn0) = alternatingGroup (Fin 5) := Y.nbrRep_map_L 0 hn0
  let x : Fin 2 ↪ ↥(Y.nbrAction 0) :=
    { toFun := Fin.cons (⟨u, (Setup.mem_nbrAction (X := Y)).mpr u.2⟩ : ↥(Y.nbrAction 0))
        (fun _ => (⟨v, (Setup.mem_nbrAction (X := Y)).mpr v.2⟩ : ↥(Y.nbrAction 0)))
      inj' := Fin.cons_injective_of_injective
        (x₀ := (⟨u, (Setup.mem_nbrAction (X := Y)).mpr u.2⟩ : ↥(Y.nbrAction 0)))
        (x := fun _ => (⟨v, (Setup.mem_nbrAction (X := Y)).mpr v.2⟩ : ↥(Y.nbrAction 0)))
        (by
          rintro ⟨i, hi⟩
          exact huv (Subtype.ext (by simpa using hi.symm)))
        (by intro i j _; exact Subsingleton.elim i j) }
  let y : Fin 2 ↪ ↥(Y.nbrAction 0) :=
    { toFun := Fin.cons (⟨u', (Setup.mem_nbrAction (X := Y)).mpr u'.2⟩ : ↥(Y.nbrAction 0))
        (fun _ => (⟨v', (Setup.mem_nbrAction (X := Y)).mpr v'.2⟩ : ↥(Y.nbrAction 0)))
      inj' := Fin.cons_injective_of_injective
        (x₀ := (⟨u', (Setup.mem_nbrAction (X := Y)).mpr u'.2⟩ : ↥(Y.nbrAction 0)))
        (x := fun _ => (⟨v', (Setup.mem_nbrAction (X := Y)).mpr v'.2⟩ : ↥(Y.nbrAction 0)))
        (by
          rintro ⟨i, hi⟩
          exact hu'v' (Subtype.ext (by simpa using hi.symm)))
        (by intro i j _; exact Subsingleton.elim i j) }
  let xE : Fin 2 ↪ Fin 5 :=
    { toFun := fun i => e (x i), inj' := fun i j h => x.inj' (e.injective h) }
  let yE : Fin 2 ↪ Fin 5 :=
    { toFun := fun i => e (y i), inj' := fun i j h => y.inj' (e.injective h) }
  haveI h3 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 5)) (Fin 5) 3 := by
    simpa using alternatingGroup.isMultiplyPretransitive (Fin 5)
  have hpre : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 5)) (Fin 5) 2 :=
    MulAction.isMultiplyPretransitive_of_le (m := 2) (n := 3) (by norm_num) (by norm_num)
  obtain ⟨σ, hσ⟩ := MulAction.isMultiplyPretransitive_iff.mp hpre xE yE
  have hσmem : (σ : Equiv.Perm (Fin 5)) ∈ Hsub.map (Y.nbrRep 0 hn0) := by
    rw [hmap]
    exact σ.2
  obtain ⟨h, hh, hval⟩ := Subgroup.mem_map.mp hσmem
  have hx : Y.nbrRep 0 hn0 h (e (x 0)) = e (y 0) := by
    have h0 := congrArg (fun f : Fin 2 ↪ Fin 5 => f 0) hσ
    simpa [xE, yE, x, y, hval, Function.Embedding.smul_apply, MulAction.subgroup_smul_def] using h0
  have hy : Y.nbrRep 0 hn0 h (e (x 1)) = e (y 1) := by
    have h1 := congrArg (fun f : Fin 2 ↪ Fin 5 => f 1) hσ
    simpa [xE, yE, x, y, hval, Function.Embedding.smul_apply, MulAction.subgroup_smul_def] using h1
  have hux : h • x 0 = y 0 := by
    apply e.injective
    rw [← Y.nbrRep_apply 0 hn0 h (x 0)]
    exact hx
  have hvx : h • x 1 = y 1 := by
    apply e.injective
    rw [← Y.nbrRep_apply 0 hn0 h (x 1)]
    exact hy
  refine ⟨(h : G), Subgroup.mem_subgroupOf.mp hh, ?_, ?_⟩
  · have := congrArg (fun w : ↥(Y.nbrAction 0) => (w : V)) hux
    simpa [x, y, MulAction.subgroup_smul_def] using this
  · have := congrArg (fun w : ↥(Y.nbrAction 0) => (w : V)) hvx
    simpa [x, y, MulAction.subgroup_smul_def] using this
private theorem card_Q_one_of_caseC (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (h5 : s = 5) : Nat.card ↥(Y.Q 1) = 2 ^ 6 := by
  have hScard : Nat.card Y.S = 2 ^ 7 := (caseC_n Y H hZ h5).2.1
  have hQ1leE : Y.Q 1 ≤ Y.edgeSylow 1 := Y.Q_le_edgeSylow_left 1
  have hedge : Nat.card (Y.edgeSylow 1) = 2 ^ 7 := by
    rw [Y.card_edgeSylow_eq 1, Y.edgeSylow_zero]
    exact hScard
  have h := Subgroup.relIndex_mul_card (H := Y.Q 1) (K := Y.edgeSylow 1)
  rw [inf_eq_left.mpr hQ1leE, Y.relIndex_Q_edgeSylow 1, H.n_one, hedge] at h
  omega

private theorem exists_Z_zero_eq_zpowers (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) :
    ∃ z ∈ Y.Z 0, z ≠ 1 ∧ z * z = 1 ∧ Y.Z 0 = Subgroup.zpowers z := by
  have hZ0card : Nat.card ↥(Y.Z 0) = 2 := (s52_step8 Y H hZ).2.2.2.2.2.2.1
  haveI hfinZ0 : Finite ↥(Y.Z 0) := Nat.finite_of_card_ne_zero (by rw [hZ0card]; norm_num)
  have hZ0ne : Y.Z 0 ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ0card
    norm_num at hZ0card
  obtain ⟨z, hzZ0, hz1⟩ := (Subgroup.bot_or_exists_ne_one (Y.Z 0)).resolve_left hZ0ne
  have hz2 : z * z = 1 := by
    have hdvd : orderOf z ∣ 2 := by
      have h := orderOf_dvd_natCard (⟨z, hzZ0⟩ : ↥(Y.Z 0))
      rwa [Subgroup.orderOf_mk, hZ0card] at h
    have hord : orderOf z = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hz1
      · exact h
    rw [← pow_two, ← hord]
    exact pow_orderOf_eq_one z
  have hZ0_zp : Y.Z 0 = Subgroup.zpowers z := by
    have hle : Subgroup.zpowers z ≤ Y.Z 0 := Subgroup.zpowers_le.mpr hzZ0
    have hcard : Nat.card ↥(Subgroup.zpowers z) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1]
    haveI : Finite ↥(Y.Z 0) := Nat.finite_of_card_ne_zero (by rw [hZ0card]; norm_num)
    have hle2 : Y.Z 0 ≤ Subgroup.zpowers z := by
      have hEq : Subgroup.zpowers z = Y.Z 0 :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hZ0card])
      exact hEq.ge
    exact le_antisymm hle2 hle
  exact ⟨z, hzZ0, hz1, hz2, hZ0_zp⟩

private theorem vertZ_nbr_le_Q_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) (u : Γ.neighborSet (Y.vert 0)) :
    vertZ (G := G) (u : V) ≤ Y.Q 0 := by
  have hVQ : Y.VNbr0 = Y.Q 0 := (caseC_n Y H hZ h5).2.2.1
  have hSupZ := VNbr0_eq_iSup Y
  have hle : vertZ (G := G) (u : V) ≤ Y.VNbr0 := by
    rw [hSupZ]
    exact le_iSup (fun u : Γ.neighborSet (Y.vert 0) => vertZ (G := G) (u : V)) u
  rwa [hVQ] at hle

private theorem vertZ_eq_Z_zero_sup_zpowers (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {u : Γ.neighborSet (Y.vert 0)} {a : G}
    (ha : a ∈ vertZ (G := G) (u : V)) (haZ : a ∉ Y.Z 0) :
    vertZ (G := G) (u : V) = Y.Z 0 ⊔ Subgroup.zpowers a := by
  have hZ0card : Nat.card ↥(Y.Z 0) = 2 := (s52_step8 Y H hZ).2.2.2.2.2.2.1
  have hZle : Y.Z 0 ≤ vertZ (G := G) (u : V) := Z_zero_le_vertZ Y H hZ u
  have hcard : Nat.card ↥(vertZ (G := G) (u : V)) = 4 := card_vertZ_nbr Y H hZ u
  haveI : Finite ↥(vertZ (G := G) (u : V)) :=
    finite_of_le_stabilizer Y.hyp
      ((vertZ_le_pCoreOf _).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _))
  exact (CFSG.Quasithin.F6.GoldAmN.sup_zpowers_eq_of_relIndex_two hZle
    (CFSG.Monster.AxisCount.relIndex_eq_two_of_card_eq hZle (by rw [hcard, hZ0card]))
    ha haZ).symm

private theorem commutator_vertZ_eq_Z_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (h5 : s = 5) (hder : ⁅Y.Q 0, Y.Q 0⁆ = Y.Z 0)
    {u v : Γ.neighborSet (Y.vert 0)} (huv : u ≠ v) :
    ⁅vertZ (G := G) (u : V), vertZ (G := G) (v : V)⁆ = Y.Z 0 := by
  have hZ0card : Nat.card ↥(Y.Z 0) = 2 := (s52_step8 Y H hZ).2.2.2.2.2.2.1
  haveI hfinZ0 : Finite ↥(Y.Z 0) := Nat.finite_of_card_ne_zero (by rw [hZ0card]; norm_num)
  have hn0 : Y.n 0 = 2 := by rw [H.n_zero, (caseC_n Y H hZ h5).1]
  have hvertZ_le_Q : ∀ u : Γ.neighborSet (Y.vert 0), vertZ (G := G) (u : V) ≤ Y.Q 0 :=
    vertZ_nbr_le_Q_zero Y H hZ h5
  have hleQ : ⁅vertZ (G := G) (u : V), vertZ (G := G) (v : V)⁆ ≤ ⁅Y.Q 0, Y.Q 0⁆ :=
    Subgroup.commutator_mono (hvertZ_le_Q u) (hvertZ_le_Q v)
  have hleZ : ⁅vertZ (G := G) (u : V), vertZ (G := G) (v : V)⁆ ≤ Y.Z 0 := by
    rwa [hder] at hleQ
  have hne : ⁅vertZ (G := G) (u : V), vertZ (G := G) (v : V)⁆ ≠ ⊥ := by
    intro hbot
    have hall : ∀ a b : Γ.neighborSet (Y.vert 0), a ≠ b →
        ⁅vertZ (G := G) (a : V), vertZ (G := G) (b : V)⁆ = ⊥ := by
      intro a b hab
      obtain ⟨g, hgL, hga, hgb⟩ := L_zero_two_trans Y hn0
        (u := u) (v := v) (u' := a) (v' := b) huv hab
      have hconj : conjSub g ⁅vertZ (G := G) (u : V), vertZ (G := G) (v : V)⁆ =
          ⁅vertZ (G := G) (a : V), vertZ (G := G) (b : V)⁆ := by
        rw [← conjSub_commutator, ← vertZ_smul (G := G) g (u : V), hga,
          ← vertZ_smul (G := G) g (v : V), hgb]
      rw [← hconj, hbot, conjSub_bot]
    have hEA : IsElemAbelian 2 (Y.Q 0) := by
      have hVQ : Y.VNbr0 = Y.Q 0 := (caseC_n Y H hZ h5).2.2.1
      have hSupZ := VNbr0_eq_iSup Y
      have hsup : Y.Q 0 = ⨆ u : Γ.neighborSet (Y.vert 0),
          vertZ (G := G) (u : V) := by rw [← hVQ, hSupZ]
      have hclosure : (⨆ u : Γ.neighborSet (Y.vert 0), vertZ (G := G) (u : V)) =
          Subgroup.closure (⋃ u : Γ.neighborSet (Y.vert 0),
            (vertZ (G := G) (u : V) : Set G)) := by
        rw [Subgroup.closure_iUnion]
        simp [Subgroup.closure_eq]
      rw [hsup, hclosure]
      refine IsElemAbelian.closure_of_commute ?_ ?_
      · intro a ha b hb
        simp only [Set.mem_iUnion] at ha hb
        obtain ⟨ua, hua⟩ := ha
        obtain ⟨ub, hub⟩ := hb
        by_cases heq : ua = ub
        · subst heq
          exact (isElemAbelian_vertZ_nbr Y H hZ ua).comm hua hub
        · have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (hall ua ub heq)) hua
          exact (Subgroup.mem_centralizer_iff.mp hle b hub).symm
      · intro a ha
        simp only [Set.mem_iUnion] at ha
        obtain ⟨u, hu⟩ := ha
        exact (isElemAbelian_vertZ_nbr Y H hZ u).2 a hu
    have hbotQ : ⁅Y.Q 0, Y.Q 0⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr hEA.1
    rw [hder] at hbotQ
    have hcard1 : Nat.card ↥(Y.Z 0) = 1 := by rw [hbotQ, Subgroup.card_bot]
    omega
  haveI : Finite ↥(⁅vertZ (G := G) (u : V), vertZ (G := G) (v : V)⁆) :=
    Finite.of_injective (Subgroup.inclusion hleZ) (Subgroup.inclusion_injective _)
  have hcardH : 2 ≤ Nat.card ↥(⁅vertZ (G := G) (u : V),
      vertZ (G := G) (v : V)⁆) := by
    have := (Subgroup.one_lt_card_iff_ne_bot (H := ⁅vertZ (G := G) (u : V),
      vertZ (G := G) (v : V)⁆)).mpr hne
    omega
  exact Subgroup.eq_of_le_of_card_ge hleZ (by rw [hZ0card]; exact hcardH)

private theorem commutator_eq_of_mem_vertZ (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (h5 : s = 5) (hder : ⁅Y.Q 0, Y.Q 0⁆ = Y.Z 0)
    (hcenter : centerOf (Y.Q 0) = Y.Z 0) {z : G} (hz2 : z * z = 1)
    (hZ0 : Y.Z 0 = Subgroup.zpowers z) {u v : Γ.neighborSet (Y.vert 0)} (huv : u ≠ v)
    {a b : G} (ha : a ∈ vertZ (G := G) (u : V)) (haZ : a ∉ Y.Z 0)
    (hb : b ∈ vertZ (G := G) (v : V)) (hbZ : b ∉ Y.Z 0) : ⁅a, b⁆ = z := by
  have hZ0_cent : ∀ a ∈ Y.Z 0, ∀ q ∈ Y.Q 0, a * q = q * a := by
    intro a ha q hq
    have haz : a ∈ centerOf (Y.Q 0) := by rw [hcenter]; exact ha
    have hzc : a ∈ Subgroup.centralizer (Y.Q 0 : Set G) := (Subgroup.mem_inf.mp haz).2
    exact (Subgroup.mem_centralizer_iff.mp hzc q hq).symm
  have hZ0_elem : ∀ a ∈ Y.Z 0, a = 1 ∨ a = z := by
    intro a ha
    exact CFSG.GH74.Uniqueness.Bender.eq_one_or_eq_of_mem_zpowers (K := G) hz2
      (by rwa [← hZ0])
  have hvertZ_le_Q : ∀ u : Γ.neighborSet (Y.vert 0), vertZ (G := G) (u : V) ≤ Y.Q 0 :=
    vertZ_nbr_le_Q_zero Y H hZ h5
  have hZu_eq : vertZ (G := G) (u : V) = Y.Z 0 ⊔ Subgroup.zpowers a :=
    vertZ_eq_Z_zero_sup_zpowers Y H hZ ha haZ
  have hcommZ : ⁅a, b⁆ ∈ Y.Z 0 := by
    have hmem := Subgroup.commutator_mem_commutator ha hb
    rw [commutator_vertZ_eq_Z_zero Y H hZ h5 hder huv] at hmem
    exact hmem
  have hne1 : ⁅a, b⁆ ≠ 1 := by
    intro h1
    have hb_cent : a ∈ Subgroup.centralizer (vertZ (G := G) (v : V) : Set G) := by
      have hgenZ : vertZ (G := G) (v : V) =
          Subgroup.closure ((Y.Z 0 : Set G) ∪ {b}) := by
        rw [vertZ_eq_Z_zero_sup_zpowers Y H hZ hb hbZ,
          Subgroup.zpowers_eq_closure, ← Subgroup.closure_eq (K := Y.Z 0),
          ← Subgroup.closure_union]
        simp
      rw [hgenZ, Subgroup.centralizer_closure]
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      rcases hc with hcZ | hcb
      · exact hZ0_cent c hcZ a (hvertZ_le_Q u ha)
      · rw [Set.mem_singleton_iff] at hcb
        subst hcb
        exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    have hZu_leC : vertZ (G := G) (u : V) ≤
        Subgroup.centralizer (vertZ (G := G) (v : V) : Set G) := by
      rw [hZu_eq]
      refine sup_le ?_ ?_
      · intro c hc
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        exact (hZ0_cent c hc d (hvertZ_le_Q v hd)).symm
      · rw [Subgroup.zpowers_le]
        exact hb_cent
    have hbot : ⁅vertZ (G := G) (u : V), vertZ (G := G) (v : V)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZu_leC
    rw [commutator_vertZ_eq_Z_zero Y H hZ h5 hder huv] at hbot
    have hcard1 : Nat.card ↥(Y.Z 0) = 1 := by rw [hbot, Subgroup.card_bot]
    have hZ0card : Nat.card ↥(Y.Z 0) = 2 := (s52_step8 Y H hZ).2.2.2.2.2.2.1
    omega
  rcases hZ0_elem _ hcommZ with h1 | hz
  · exact absurd h1 hne1
  · exact hz

private theorem closure_five_eq_top (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) {z : G} (hzQ : z ∈ Y.Q 0) (hZ0 : Y.Z 0 = Subgroup.zpowers z)
    {u : Fin 5 → Γ.neighborSet (Y.vert 0)} (hu : Function.Surjective u) {x : Fin 5 → G}
    (hxQ : ∀ i, x i ∈ Y.Q 0)
    (hx : ∀ i, vertZ (G := G) (u i : V) = Y.Z 0 ⊔ Subgroup.zpowers (x i)) :
    Subgroup.closure (insert (⟨z, hzQ⟩ : ↥(Y.Q 0))
      (Set.range fun i => (⟨x i, hxQ i⟩ : ↥(Y.Q 0)))) = ⊤ := by
  have hVQ : Y.VNbr0 = Y.Q 0 := (caseC_n Y H hZ h5).2.2.1
  have hSupZ := VNbr0_eq_iSup Y
  have hvertZ_le_Q : ∀ u : Γ.neighborSet (Y.vert 0), vertZ (G := G) (u : V) ≤ Y.Q 0 :=
    vertZ_nbr_le_Q_zero Y H hZ h5
  let w : Fin 5 → ↥(Y.Q 0) := fun i => ⟨x i, hxQ i⟩
  let zQ : ↥(Y.Q 0) := ⟨z, hzQ⟩
  let S : Set ↥(Y.Q 0) := insert zQ (Set.range w)
  have hZi_le : ∀ i, (vertZ (G := G) (u i : V)).subgroupOf (Y.Q 0) ≤
      Subgroup.closure S := by
    intro i
    rw [hx i]
    rw [Subgroup.subgroupOf_sup (Y.Z_le_Q 0) (Subgroup.zpowers_le.mpr (hxQ i))]
    have hZ0_sub : (Y.Z 0).subgroupOf (Y.Q 0) = Subgroup.zpowers zQ := by
      apply Subgroup.map_injective (Y.Q 0).subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (Y.Z_le_Q 0), hZ0, MonoidHom.map_zpowers]
      rfl
    have hxi_sub (i : Fin 5) : (Subgroup.zpowers (x i)).subgroupOf (Y.Q 0) =
        Subgroup.zpowers (w i) := by
      apply Subgroup.map_injective (Y.Q 0).subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr (hxQ i)),
        MonoidHom.map_zpowers]
      rfl
    rw [hZ0_sub, hxi_sub i]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp [S])
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp [S, w])
  have hQsup : Y.Q 0 = ⨆ u : Γ.neighborSet (Y.vert 0), vertZ (G := G) (u : V) := by
    rw [← hVQ, hSupZ]
  have hQclosure : Y.Q 0 = Subgroup.closure (⋃ u : Γ.neighborSet (Y.vert 0),
      (vertZ (G := G) (u : V) : Set G)) := by
    rw [hQsup, Subgroup.closure_iUnion]
    simp [Subgroup.closure_eq]
  have hQle : Y.Q 0 ≤ (Subgroup.closure S).map (Y.Q 0).subtype := by
    conv_lhs => rw [hQclosure]
    rw [Subgroup.closure_le]
    intro a ha
    simp only [Set.mem_iUnion] at ha
    obtain ⟨u, hu_mem⟩ := ha
    obtain ⟨i, rfl⟩ := hu u
    exact Subgroup.mem_map.mpr
      ⟨⟨a, hvertZ_le_Q (u i) hu_mem⟩, hZi_le i (Subgroup.mem_subgroupOf.mpr hu_mem), rfl⟩
  have hmap_closure : (Subgroup.closure S).map (Y.Q 0).subtype = Y.Q 0 := by
    apply le_antisymm
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
      exact b.2
    · exact hQle
  have hgen : Subgroup.closure S = ⊤ :=
    Subgroup.map_injective (Y.Q 0).subtype_injective
      (by rw [hmap_closure, Subgroup.map_top, Subgroup.range_subtype])
  simpa [S, w, zQ] using hgen

private theorem prod_mem_center_of_fiveRel {P : Type*} [Group P] {z : P} {w : Fin 5 → P}
    (h : CFSG.Quasithin.F112J2.FiveRel z w)
    (hgen : Subgroup.closure (insert z (Set.range w)) = ⊤) :
    w 0 * w 1 * w 2 * w 3 * w 4 ∈ Subgroup.center P := by
  let y : P := w 0 * w 1 * w 2 * w 3 * w 4
  change y ∈ Subgroup.center P
  rw [Subgroup.mem_center_iff]
  intro g
  have hle : Subgroup.closure (insert z (Set.range w)) ≤
      Subgroup.centralizer ({y} : Set P) := by
    rw [Subgroup.closure_le]
    rintro t (rfl | ⟨i, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (h.hzc y).symm
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact h.commute_prod i
  have hg : g ∈ Subgroup.centralizer ({y} : Set P) := by
    have htop : g ∈ Subgroup.closure (insert z (Set.range w)) := by
      rw [hgen]
      exact Subgroup.mem_top g
    exact hle htop
  exact Subgroup.mem_centralizer_singleton_iff.mp hg

private theorem center_Q_zero_eq_zpowers (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (hcenter : centerOf (Y.Q 0) = Y.Z 0) {z : G} (hzQ : z ∈ Y.Q 0)
    (hzZ : z ∈ Y.Z 0) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    Subgroup.center ↥(Y.Q 0) = Subgroup.zpowers (⟨z, hzQ⟩ : ↥(Y.Q 0)) := by
  haveI : Finite ↥(Y.Q 0) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 0)
  have hZ0card : Nat.card ↥(Y.Z 0) = 2 := (s52_step8 Y H hZ).2.2.2.2.2.2.1
  have hzc : ∀ q ∈ Y.Q 0, z * q = q * z := by
    intro q hq
    have hzcenter : z ∈ centerOf (Y.Q 0) := by rw [hcenter]; exact hzZ
    have hzcent : z ∈ Subgroup.centralizer (Y.Q 0 : Set G) := (Subgroup.mem_inf.mp hzcenter).2
    exact (Subgroup.mem_centralizer_iff.mp hzcent q hq).symm
  have hcenter_map : centerOf (Y.Q 0) =
      (Subgroup.center ↥(Y.Q 0)).map (Y.Q 0).subtype :=
    (CFSG.center_map_subtype_eq_inf_centralizer (Y.Q 0)).symm
  have hcard_center : Nat.card ↥(Subgroup.center ↥(Y.Q 0)) = 2 := by
    have h := Subgroup.card_map_of_injective
      (K := Subgroup.center ↥(Y.Q 0)) (Y.Q 0).subtype_injective
    rw [← h, ← hcenter_map, hcenter, hZ0card]
  let zQ : ↥(Y.Q 0) := ⟨z, hzQ⟩
  have hzQ2 : zQ * zQ = 1 := Subtype.ext hz2
  have hzQne : zQ ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzQcenter : zQ ∈ Subgroup.center ↥(Y.Q 0) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hzc g.val g.2).symm
  have hcard_zp : Nat.card ↥(Subgroup.zpowers zQ) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rwa [pow_two]) hzQne]
  have hcenter_zp : Subgroup.center ↥(Y.Q 0) = Subgroup.zpowers zQ :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzQcenter)
      (by rw [hcard_center, hcard_zp])).symm
  simpa [zQ] using hcenter_zp

private theorem caseC_q8d8 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) : IsQ8D8 ↥(Y.Q 0) := by
  have hcase := caseC_n Y H hZ h5
  have hn0 : Y.n 0 = 2 := by rw [H.n_zero, hcase.1]
  have hVQ : Y.VNbr0 = Y.Q 0 := hcase.2.2.1
  haveI hfinQ0 : Finite ↥(Y.Q 0) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 0)
  obtain ⟨z, hzZ0, hz1, hz2, hZ0_zp⟩ := exists_Z_zero_eq_zpowers Y H hZ
  have hzQ : z ∈ Y.Q 0 := Y.Z_le_Q 0 hzZ0
  have hcenterQ : centerOf (Y.Q 0) = Y.Z 0 := centerOf_Q_zero_of_VNbr0_eq Y H hZ hVQ
  have hzc : ∀ q ∈ Y.Q 0, z * q = q * z := by
    intro q hq
    have hzcenter : z ∈ centerOf (Y.Q 0) := by rw [hcenterQ]; exact hzZ0
    have hzcent : z ∈ Subgroup.centralizer (Y.Q 0 : Set G) :=
      (Subgroup.mem_inf.mp hzcenter).2
    exact (Subgroup.mem_centralizer_iff.mp hzcent q hq).symm
  have hder : ⁅Y.Q 0, Y.Q 0⁆ = Y.Z 0 := commutator_Q_zero_eq_Z_zero Y H hZ
  set wOf : Fin 5 → ↥(Y.nbrAction 0) := fun i => (Y.nbrEquiv 0 hn0).symm i with hwOf
  set uOf : Fin 5 → Γ.neighborSet (Y.vert 0) := fun i =>
    ⟨(wOf i : V), (Setup.mem_nbrAction (X := Y)).mp (wOf i).2⟩ with huOf
  have huOf_inj : Function.Injective uOf := by
    intro i j hij
    have hval : (wOf i : V) = (wOf j : V) := by
      have := congrArg Subtype.val hij
      simpa [huOf] using this
    exact (Y.nbrEquiv 0 hn0).symm.injective (Subtype.ext hval)
  have huOf_surj : Function.Surjective uOf := by
    intro u
    let w : ↥(Y.nbrAction 0) := ⟨u, (Setup.mem_nbrAction (X := Y)).mpr u.2⟩
    refine ⟨(Y.nbrEquiv 0 hn0) w, ?_⟩
    apply Subtype.ext
    simp [huOf, hwOf, w]
  set xOf5 : Fin 5 → G := fun i => xOf Y H hZ (uOf i) with hxOf5
  have hx_mem : ∀ i, xOf5 i ∈ vertZ (G := G) (uOf i : V) := fun i =>
    (xOf_spec Y H hZ (uOf i)).1
  have hx_not : ∀ i, xOf5 i ∉ Y.Z 0 := fun i => (xOf_spec Y H hZ (uOf i)).2
  have hx2 : ∀ i, xOf5 i * xOf5 i = 1 := by
    intro i
    exact (isElemAbelian_vertZ_nbr Y H hZ (uOf i)).mul_self_eq_one (hx_mem i)
  have hxQ : ∀ i, xOf5 i ∈ Y.Q 0 := fun i =>
    vertZ_nbr_le_Q_zero Y H hZ h5 (uOf i) (hx_mem i)
  have hZu_eq : ∀ i, vertZ (G := G) (uOf i : V) =
      Y.Z 0 ⊔ Subgroup.zpowers (xOf5 i) := fun i =>
    vertZ_eq_Z_zero_sup_zpowers Y H hZ (hx_mem i) (hx_not i)
  have hxixj : ∀ i j : Fin 5, i ≠ j → ⁅xOf5 i, xOf5 j⁆ = z := fun i j hij =>
    commutator_eq_of_mem_vertZ Y H hZ h5 hder hcenterQ hz2 hZ0_zp
      (huOf_inj.ne hij) (hx_mem i) (hx_not i) (hx_mem j) (hx_not j)
  let w : Fin 5 → ↥(Y.Q 0) := fun i => ⟨xOf5 i, hxQ i⟩
  let zQ : ↥(Y.Q 0) := ⟨z, hzQ⟩
  have hFive : CFSG.Quasithin.F112J2.FiveRel (P := ↥(Y.Q 0)) zQ w := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hz1 (congrArg Subtype.val h)
    · exact Subtype.ext hz2
    · intro q
      apply Subtype.ext
      exact (hzc q.val q.2).symm
    · intro i
      exact Subtype.ext (hx2 i)
    · intro i j hij
      apply Subtype.ext
      show xOf5 i * xOf5 j = z * (xOf5 j * xOf5 i)
      calc xOf5 i * xOf5 j = ⁅xOf5 i, xOf5 j⁆ * (xOf5 j * xOf5 i) := by
            rw [commutatorElement_def]; group
        _ = z * (xOf5 j * xOf5 i) := by rw [hxixj i j hij]
  have hgen : Subgroup.closure (insert zQ (Set.range w)) = ⊤ := by
    simpa [w, zQ] using
      closure_five_eq_top Y H hZ h5 hzQ hZ0_zp huOf_surj hxQ hZu_eq
  have hcenter_zp : Subgroup.center ↥(Y.Q 0) = Subgroup.zpowers zQ := by
    simpa [zQ] using center_Q_zero_eq_zpowers Y H hZ hcenterQ hzQ hzZ0 hz1 hz2
  have hy : w 0 * w 1 * w 2 * w 3 * w 4 ∈ Subgroup.zpowers zQ := by
    rw [← hcenter_zp]
    exact prod_mem_center_of_fiveRel hFive hgen
  exact hFive.isQ8D8 hy hgen

private theorem caseC_nat (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) : NatSec (Y.L 1) ⊥ (Y.Q 1) := by
  intro x hxL hx3
  intro e heQ hcomm
  have hA : Y.Q 0 ⊓ Y.Q 2 = Y.Z 1 := (caseC_n Y H hZ h5).2.2.2
  have hstep := s52_step10 Y H hZ hxL hx3
  have hcent : e ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa using hcomm)
  have heA : e ∈ Y.Q 0 ⊓ Y.Q 2 := hstep.1 e heQ hcent
  have heZ : e ∈ Y.Z 1 := by
    have h := heA
    rwa [hA] at h
  have hAexp := s52_A_eq Y H hZ hxL hx3
  have hebot : e ∈ (Y.Q 0 ⊓ Y.Q 2 ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ Y.Z 1 :=
    ⟨⟨heA, hcent⟩, heZ⟩
  rw [hAexp.2] at hebot
  simpa using hebot

private theorem sup_inf_K_eq (Y : Setup Γ G) {F : Subgroup G}
    (hFle : F ≤ Y.Gi 0 ⊓ Y.Gi 1) (hSF : Y.S ≤ F) :
    F = Y.S ⊔ (F ⊓ Y.K) := by
  apply le_antisymm
  · intro x hx
    have hxG : x ∈ Y.Gi 0 ⊓ Y.Gi 1 := hFle hx
    have hxKS : x ∈ Y.K ⊔ Y.S := by rw [Y.K_sup]; exact hxG
    have hKnormS : Y.K ≤ Subgroup.normalizer (Y.S : Set G) := by
      rw [← Y.edgeSylow_zero]
      exact (le_inf (Y.K_le_Gi 0) (Y.K_le_Gi 1)).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0 ⊓ Y.Gi 1))
    have hxmul : x ∈ (Y.K : Set G) * (Y.S : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y.K Y.S hKnormS]
      exact hxKS
    obtain ⟨kk, hkkK, ss, hssS, hkk⟩ := hxmul
    have hkkF : kk ∈ F := by
      have hkk' : kk * ss = x := hkk
      have : kk = x * ss⁻¹ := by rw [← hkk']; group
      rw [this]
      exact F.mul_mem hx (F.inv_mem (hSF hssS))
    rw [← hkk, sup_comm]
    exact Subgroup.mul_mem_sup ⟨hkkF, hkkK⟩ hssS
  · exact sup_le hSF inf_le_left

private theorem isComplement_subgroupOf_of_sup {A B F : Subgroup G} (hAF : A ≤ F) (hBF : B ≤ F)
    (hAn : (A.subgroupOf F).Normal) (hsup : A ⊔ B = F) (hinf : A ⊓ B = ⊥) :
    (A.subgroupOf F).IsComplement' (B.subgroupOf F) := by
  haveI := hAn
  have hsup' : (A.subgroupOf F) ⊔ (B.subgroupOf F) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAF hBF, hsup, Subgroup.subgroupOf_self]
  have hinf' : (A.subgroupOf F) ⊓ (B.subgroupOf F) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
    have hxbot : ((x : ↥F) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hinf]
      exact ⟨Subgroup.mem_subgroupOf.mp hxA, Subgroup.mem_subgroupOf.mp hxB⟩
    exact Subgroup.mem_bot.mpr (Subtype.ext (by simpa using hxbot))
  exact Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf')
    (by rw [← Subgroup.normal_mul, hsup', Subgroup.coe_top])

private theorem exists_S_conj_mem_K (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) {k : G} (hkG : k ∈ Y.Gi 0 ⊓ Y.Gi 1) (hk3 : orderOf k = 3) :
    ∃ s ∈ Y.S, s * k * s⁻¹ ∈ Y.K := by
  have hScard : Nat.card Y.S = 2 ^ 7 := (caseC_n Y H hZ h5).2.1
  let T : Subgroup G := Subgroup.zpowers k
  let F : Subgroup G := Y.S ⊔ T
  let N : Subgroup ↥F := Y.S.subgroupOf F
  let Hc : Subgroup ↥F := T.subgroupOf F
  let Kc : Subgroup ↥F := (F ⊓ Y.K).subgroupOf F
  have hTle : T ≤ Y.Gi 0 ⊓ Y.Gi 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ⟨(Y.Gi 0).zpow_mem hkG.1 m, (Y.Gi 1).zpow_mem hkG.2 m⟩
  have hSle : Y.S ≤ Y.Gi 0 ⊓ Y.Gi 1 := (Y.isSylowTwoOf_edgeSylow 0).1
  haveI : Finite ↥Y.S := finite_of_le_stabilizer Y.hyp (hSle.trans inf_le_left)
  have hFle : F ≤ Y.Gi 0 ⊓ Y.Gi 1 := sup_le hSle hTle
  haveI : Finite ↥F := finite_of_le_stabilizer Y.hyp (hFle.trans inf_le_left)
  have hSnormG : Y.Gi 0 ⊓ Y.Gi 1 ≤ Subgroup.normalizer (Y.S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSle).mp
      (by simpa [Y.edgeSylow_zero] using Y.edgeSylow_subgroupOf_normal 0)
  have hNnormal : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : Y.S ≤ F)).2
      (hFle.trans hSnormG)
  have hcardT : Nat.card ↥T = 3 := by
    rw [show T = Subgroup.zpowers k from rfl, Nat.card_zpowers, hk3]
  have hdisjST : Disjoint Y.S T :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hScard, hcardT]; norm_num)
  have hinfST : Y.S ⊓ T = ⊥ := disjoint_iff.mp hdisjST
  have hNHcomp : Subgroup.IsComplement' N Hc :=
    isComplement_subgroupOf_of_sup le_sup_left le_sup_right hNnormal rfl hinfST
  have hFsup : F = Y.S ⊔ (F ⊓ Y.K) := sup_inf_K_eq Y hFle le_sup_left
  have hinfKS : Y.S ⊓ (F ⊓ Y.K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxF, hxK⟩ := hx
    have hbot : x ∈ (⊥ : Subgroup G) := by
      rw [← Y.K_inf]
      exact Subgroup.mem_inf.mpr ⟨hxK, hxS⟩
    simpa using hbot
  have hNKcomp : Subgroup.IsComplement' N Kc :=
    isComplement_subgroupOf_of_sup le_sup_left inf_le_left hNnormal hFsup.symm hinfKS
  have hSFnorm : T ≤ Subgroup.normalizer (Y.S : Set G) := hTle.trans hSnormG
  have hcardF : Nat.card ↥F = Nat.card ↥Y.S * 3 := by
    have h :=
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Y.S T hSFnorm hdisjST
    rw [hcardT] at h
    exact h
  have hcardN : Nat.card ↥N = Nat.card ↥Y.S := by
    rw [show N = Y.S.subgroupOf F from rfl]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : Y.S ≤ F)).toEquiv
  have hindexN : N.index = 3 := by
    have h := Subgroup.card_mul_index N
    rw [hcardN, hcardF] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hcopN : Nat.Coprime (Nat.card ↥N) N.index := by
    rw [hcardN, hindexN, hScard]
    norm_num
  obtain ⟨n, hn⟩ :=
    _root_.CFSG.GorensteinWalter.SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
      N Hc Kc hNnormal hNHcomp hNKcomp hcopN
  let s : G := ((n : ↥F) : G)
  refine ⟨s, n.2, ?_⟩
  have hkF : k ∈ F := Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
  have hkH : (⟨k, hkF⟩ : ↥F) ∈ Hc := by
    change k ∈ T
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  have hkmap : (MulAut.conj (n : ↥F)) ⟨k, hkF⟩ ∈ Kc := by
    rw [hn]
    exact Subgroup.mem_map_of_mem _ hkH
  have hkmapK : ((MulAut.conj (n : ↥F)) ⟨k, hkF⟩ : ↥F) ∈ (F ⊓ Y.K).subgroupOf F := hkmap
  have hk0val : (((MulAut.conj (n : ↥F)) ⟨k, hkF⟩ : ↥F) : G) = s * k * s⁻¹ := by
    simp [MulAut.conj_apply, s]
  rw [← hk0val]
  exact (Subgroup.mem_subgroupOf.mp hkmapK).2

private theorem caseC_cent3 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) :
    ∀ k ∈ Y.Gi 0 ⊓ Y.Gi 1, orderOf k = 3 →
      Y.Q 1 ⊓ Subgroup.centralizer ({k} : Set G) = Y.Z 1 := by
  intro k hkG hk3
  have hA : Y.Q 0 ⊓ Y.Q 2 = Y.Z 1 := (caseC_n Y H hZ h5).2.2.2
  obtain ⟨s, hsS, hskK⟩ := exists_S_conj_mem_K Y H hZ h5 hkG hk3
  have hSle : Y.S ≤ Y.Gi 0 ⊓ Y.Gi 1 := (Y.isSylowTwoOf_edgeSylow 0).1
  set k0 : G := s * k * s⁻¹ with hk0def
  have hk0K : k0 ∈ Y.K := by rw [hk0def]; exact hskK
  have hk0ne : k0 ≠ 1 := by
    intro h
    have hk1 : k = 1 := by
      have hconj : s⁻¹ * k0 * s = k := by rw [hk0def]; group
      rw [← hconj, h]; group
    rw [hk1] at hk3
    simp at hk3
  have hZt1 : Y.Zt 1 = ⊥ := (s52_step8 Y H hZ).2.2.2.2.2.2.2
  have hZleCk0 : Y.Z 1 ≤ Subgroup.centralizer ({k0} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmem : ⁅z, k0⁆ ∈ Y.Zt 1 := Subgroup.commutator_mem_commutator hz hk0K
    rw [hZt1] at hmem
    have h1 : ⁅z, k0⁆ = 1 := by simpa using hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hQ1Ck0 : Y.Q 1 ⊓ Subgroup.centralizer ({k0} : Set G) = Y.Z 1 := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hx' := Q_one_inf_centralizer_le Y H hk0K hk0ne hx
      have h := hx'
      rw [hA] at h
      exact h
    · intro z hz
      exact Subgroup.mem_inf.mpr ⟨Y.Z_le_Q 1 hz, hZleCk0 hz⟩
  have hsG1 : s ∈ Y.Gi 1 := (hSle hsS).2
  have hcent_iff : ∀ x : G, x ∈ Subgroup.centralizer ({k} : Set G) ↔
      s * x * s⁻¹ ∈ Subgroup.centralizer ({k0} : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : s * (x * k) * s⁻¹ = s * (k * x) * s⁻¹ := by rw [h]
      calc (s * x * s⁻¹) * k0 = s * (x * k) * s⁻¹ := by rw [hk0def]; group
        _ = s * (k * x) * s⁻¹ := h'
        _ = k0 * (s * x * s⁻¹) := by rw [hk0def]; group
    · intro h
      have h' : s * (x * k) * s⁻¹ = s * (k * x) * s⁻¹ := by
        rw [hk0def] at h
        calc s * (x * k) * s⁻¹ = (s * x * s⁻¹) * (s * k * s⁻¹) := by group
          _ = (s * k * s⁻¹) * (s * x * s⁻¹) := h
          _ = s * (k * x) * s⁻¹ := by group
      calc x * k = s⁻¹ * (s * (x * k) * s⁻¹) * s := by group
        _ = s⁻¹ * (s * (k * x) * s⁻¹) * s := by rw [h']
        _ = k * x := by group
  have hQ1s : conjSub s (Y.Q 1) = Y.Q 1 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1) hsG1)
  have hCk : conjSub s (Subgroup.centralizer ({k} : Set G)) =
      Subgroup.centralizer ({k0} : Set G) := by
    ext x
    rw [mem_conjSub, hcent_iff, show s * (s⁻¹ * x * s) * s⁻¹ = x by group]
  refine (conjSub_inj s).mp ?_
  rw [conjSub_inf, hQ1s, hCk, hQ1Ck0, Y.Z_normal 1 s hsG1]

private theorem card_sup_mul_card_inf_of_le_normal {H K L : Subgroup G} [Finite ↥L]
    (hH : H ≤ L) (hK : K ≤ L) (hKn : (K.subgroupOf L).Normal) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  have hnorm : H.subgroupOf L ≤ Subgroup.normalizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hKn]
    exact le_top
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := H.subgroupOf L) (K := K.subgroupOf L) hnorm
  have hsup : (H.subgroupOf L) ⊔ (K.subgroupOf L) = (H ⊔ K).subgroupOf L :=
    (Subgroup.subgroupOf_sup hH hK).symm
  have hinf : (H.subgroupOf L) ⊓ (K.subgroupOf L) = (H ⊓ K).subgroupOf L := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [hsup, hinf] at h
  have h1 : Nat.card ↥((H ⊔ K).subgroupOf L) = Nat.card ↥(H ⊔ K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hH hK)).toEquiv
  have h2 : Nat.card ↥((H ⊓ K).subgroupOf L) = Nat.card ↥(H ⊓ K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hH)).toEquiv
  have h3 : Nat.card ↥(H.subgroupOf L) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have h4 : Nat.card ↥(K.subgroupOf L) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  rwa [h1, h2, h3, h4] at h

private theorem sq_mem_Z_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {x : G} (hx : x ∈ Y.Q 0) : x * x ∈ Y.Z 0 := by
  have hds : dsFrattini (Y.Q 0) = Y.Z 0 := dsFrattini_Q_zero_eq_Z_zero Y H hZ
  haveI : Finite ↥(Y.Q 0) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 0)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥(Y.Q 0)) := ⟨pCoreOf_isPGroup' (Y.Gi 0)⟩
  have hx' : (⟨x, hx⟩ : ↥(Y.Q 0)) ^ 2 ∈ frattini ↥(Y.Q 0) :=
    CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) (R := ↥(Y.Q 0)) ⟨x, hx⟩
  have hmem : x ^ 2 ∈ dsFrattini (Y.Q 0) := ⟨_, hx', rfl⟩
  rw [hds] at hmem
  simpa [pow_two] using hmem

private theorem commutator_mem_Z_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {x y : G} (hx : x ∈ Y.Q 0) (hy : y ∈ Y.Q 0) :
    ⁅x, y⁆ ∈ Y.Z 0 := by
  have hder : ⁅Y.Q 0, Y.Q 0⁆ = Y.Z 0 := commutator_Q_zero_eq_Z_zero Y H hZ
  have hmem := Subgroup.commutator_mem_commutator hx hy
  rwa [hder] at hmem

private theorem Q_two_eq_conj (Y : Setup Γ G) :
    Y.Q 2 = conjSub (Y.τ ^ (1 : ℤ)) (Y.Q 0) := by
  simpa using Y.Q_add 1 0

private theorem Z_two_eq_conj (Y : Setup Γ G) :
    Y.Z 2 = conjSub (Y.τ ^ (1 : ℤ)) (Y.Z 0) := by
  simpa using Y.Z_add 1 0

private theorem sq_mem_Z_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {x : G} (hx : x ∈ Y.Q 2) : x * x ∈ Y.Z 2 := by
  rw [Q_two_eq_conj] at hx
  change x ∈ (Y.Q 0).map (MulAut.conj (Y.τ ^ (1 : ℤ))).toMonoidHom at hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy2 : y * y ∈ Y.Z 0 := sq_mem_Z_zero Y H hZ hy
  rw [Z_two_eq_conj]
  refine Subgroup.mem_map.mpr ⟨y * y, hy2, ?_⟩
  simp [map_mul]

private theorem commutator_mem_Z_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {x y : G} (hx : x ∈ Y.Q 2) (hy : y ∈ Y.Q 2) :
    ⁅x, y⁆ ∈ Y.Z 2 := by
  rw [Q_two_eq_conj] at hx hy
  change x ∈ (Y.Q 0).map (MulAut.conj (Y.τ ^ (1 : ℤ))).toMonoidHom at hx
  change y ∈ (Y.Q 0).map (MulAut.conj (Y.τ ^ (1 : ℤ))).toMonoidHom at hy
  rw [Subgroup.mem_map] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have hab : ⁅a, b⁆ ∈ Y.Z 0 := commutator_mem_Z_zero Y H hZ ha hb
  rw [Z_two_eq_conj]
  refine Subgroup.mem_map.mpr ⟨⁅a, b⁆, hab, ?_⟩
  simp [map_commutatorElement]

private theorem Q_one_le_normalizer_Q_inf_Q_one (Y : Setup Γ G) {j : ℤ}
    (hj : Y.Q 1 ≤ Y.Gi j) :
    Y.Q 1 ≤ Subgroup.normalizer ((Y.Q j ⊓ Y.Q 1 : Subgroup G) : Set G) :=
  (le_inf (hj.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi j)))
    (Y.Q 1).le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf

private theorem commutator_self_Q_one_le_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (hderQ0 : ⁅Y.Q 0, Y.Q 0⁆ = Y.Z 0)
    (hAB : ⁅Y.Q 0 ⊓ Y.Q 1, Y.Q 2 ⊓ Y.Q 1⁆ ≤ Y.Z 1) : ⁅Y.Q 1, Y.Q 1⁆ ≤ Y.Z 1 := by
  have hderQ2 : ⁅Y.Q 2, Y.Q 2⁆ ≤ Y.Z 2 := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact commutator_mem_Z_two Y H hZ hx hy
  have hZ1eq : Y.Z 1 = Y.Z 0 ⊔ Y.Z 2 := (s52_step8 Y H hZ).2.2.2.2.1
  have hZ0leZ1 : Y.Z 0 ≤ Y.Z 1 := by rw [hZ1eq]; exact le_sup_left
  have hZ2leZ1 : Y.Z 2 ≤ Y.Z 1 := by rw [hZ1eq]; exact le_sup_right
  let A : Subgroup G := Y.Q 0 ⊓ Y.Q 1
  let B : Subgroup G := Y.Q 2 ⊓ Y.Q 1
  have hA_le_Q1 : A ≤ Y.Q 1 := inf_le_right
  have hB_le_Q1 : B ≤ Y.Q 1 := inf_le_right
  have hQ1NA : Y.Q 1 ≤ Subgroup.normalizer (A : Set G) :=
    Q_one_le_normalizer_Q_inf_Q_one Y (j := 0)
      (by simpa using (Y.Q_le_Gi_adj 1).trans inf_le_left)
  have hQ1NB : Y.Q 1 ≤ Subgroup.normalizer (B : Set G) :=
    Q_one_le_normalizer_Q_inf_Q_one Y (j := 2)
      (by simpa using (Y.Q_le_Gi_adj 1).trans inf_le_right)
  haveI hAnorm : (A.subgroupOf (Y.Q 1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA_le_Q1).mpr hQ1NA
  haveI hBnorm : (B.subgroupOf (Y.Q 1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hB_le_Q1).mpr hQ1NB
  have hAA : ⁅A.subgroupOf (Y.Q 1), A.subgroupOf (Y.Q 1)⁆ ≤
      (Y.Z 1).subgroupOf (Y.Q 1) := by
    rw [← Subgroup.map_le_map_iff_of_injective (Y.Q 1).subtype_injective]
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA_le_Q1,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Y.Z_le_Q 1)]
    calc ⁅A, A⁆ ≤ ⁅Y.Q 0, Y.Q 0⁆ := Subgroup.commutator_mono inf_le_left inf_le_left
      _ = Y.Z 0 := hderQ0
      _ ≤ Y.Z 1 := hZ0leZ1
  have hBB : ⁅B.subgroupOf (Y.Q 1), B.subgroupOf (Y.Q 1)⁆ ≤
      (Y.Z 1).subgroupOf (Y.Q 1) := by
    rw [← Subgroup.map_le_map_iff_of_injective (Y.Q 1).subtype_injective]
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hB_le_Q1,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Y.Z_le_Q 1)]
    calc ⁅B, B⁆ ≤ ⁅Y.Q 2, Y.Q 2⁆ := Subgroup.commutator_mono inf_le_left inf_le_left
      _ ≤ Y.Z 2 := hderQ2
      _ ≤ Y.Z 1 := hZ2leZ1
  have hABq : ⁅A.subgroupOf (Y.Q 1), B.subgroupOf (Y.Q 1)⁆ ≤
      (Y.Z 1).subgroupOf (Y.Q 1) := by
    rw [← Subgroup.map_le_map_iff_of_injective (Y.Q 1).subtype_injective]
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA_le_Q1,
      Subgroup.map_subgroupOf_eq_of_le hB_le_Q1,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Y.Z_le_Q 1)]
    exact hAB
  have hABsup : A ⊔ B = Y.Q 1 := (Q_eq_sup_inf Y H 1).symm
  have hsupq : A.subgroupOf (Y.Q 1) ⊔ B.subgroupOf (Y.Q 1) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hA_le_Q1 hB_le_Q1, hABsup, Subgroup.subgroupOf_self]
  have hQ1q : ⁅(⊤ : Subgroup ↥(Y.Q 1)), (⊤ : Subgroup ↥(Y.Q 1))⁆ ≤
      (Y.Z 1).subgroupOf (Y.Q 1) := by
    rw [← hsupq]
    rw [Subgroup.commutator_sup_left, Subgroup.commutator_sup_right,
      Subgroup.commutator_sup_right]
    refine sup_le (sup_le hAA ?_) (sup_le hABq hBB)
    exact (le_of_eq (Subgroup.commutator_comm _ _)).trans hABq
  have hQ1comm : ⁅Y.Q 1, Y.Q 1⁆ ≤ Y.Z 1 := by
    have htopmap : (⁅(⊤ : Subgroup ↥(Y.Q 1)), (⊤ : Subgroup ↥(Y.Q 1))⁆).map
        (Y.Q 1).subtype = ⁅Y.Q 1, Y.Q 1⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    have hZmap : ((Y.Z 1).subgroupOf (Y.Q 1)).map (Y.Q 1).subtype = Y.Z 1 := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Y.Z_le_Q 1)]
    rw [← htopmap, ← hZmap]
    exact (Subgroup.map_le_map_iff_of_injective (f := (Y.Q 1).subtype)
      (Y.Q 1).subtype_injective).mpr hQ1q
  exact hQ1comm

private theorem mul_self_mem_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (hAB : ⁅Y.Q 0 ⊓ Y.Q 1, Y.Q 2 ⊓ Y.Q 1⁆ ≤ Y.Z 1) :
    ∀ x ∈ Y.Q 1, x * x ∈ Y.Z 1 := by
  intro x hx
  have hZ1eq : Y.Z 1 = Y.Z 0 ⊔ Y.Z 2 := (s52_step8 Y H hZ).2.2.2.2.1
  have hZ0leZ1 : Y.Z 0 ≤ Y.Z 1 := by rw [hZ1eq]; exact le_sup_left
  have hZ2leZ1 : Y.Z 2 ≤ Y.Z 1 := by rw [hZ1eq]; exact le_sup_right
  let A : Subgroup G := Y.Q 0 ⊓ Y.Q 1
  let B : Subgroup G := Y.Q 2 ⊓ Y.Q 1
  have hA_le_Q1 : A ≤ Y.Q 1 := inf_le_right
  have hB_le_Q1 : B ≤ Y.Q 1 := inf_le_right
  have hQ1NA : Y.Q 1 ≤ Subgroup.normalizer (A : Set G) :=
    Q_one_le_normalizer_Q_inf_Q_one Y (j := 0)
      (by simpa using (Y.Q_le_Gi_adj 1).trans inf_le_left)
  have hABsup : A ⊔ B = Y.Q 1 := (Q_eq_sup_inf Y H 1).symm
  have hBnormA : B ≤ Subgroup.normalizer (A : Set G) := hB_le_Q1.trans hQ1NA
  have hcoe : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A B hBnormA
  rw [← hABsup] at hx
  change x ∈ ((A ⊔ B : Subgroup G) : Set G) at hx
  rw [hcoe, Set.mem_mul] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have ha2 : a * a ∈ Y.Z 0 := sq_mem_Z_zero Y H hZ ha.1
  have hb2 : b * b ∈ Y.Z 2 := sq_mem_Z_two Y H hZ hb.1
  have hcomm : ⁅a⁻¹, b⁆ ∈ Y.Z 1 :=
    hAB (Subgroup.commutator_mem_commutator (A.inv_mem ha) hb)
  have hEq : (a * b) * (a * b) = (a * a) * ⁅a⁻¹, b⁆ * (b * b) := by
    rw [commutatorElement_def]
    group
  rw [hEq]
  exact (Y.Z 1).mul_mem ((Y.Z 1).mul_mem (hZ0leZ1 ha2) hcomm) (hZ2leZ1 hb2)

private theorem isElemSec_Z_one_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (h5 : s = 5) : IsElemSec (Y.Z 1) (Y.Q 1) := by
  have hderQ0 : ⁅Y.Q 0, Y.Q 0⁆ = Y.Z 0 := commutator_Q_zero_eq_Z_zero Y H hZ
  have hQ1NA : Y.Q 1 ≤ Subgroup.normalizer ((Y.Q 0 ⊓ Y.Q 1 : Subgroup G) : Set G) :=
    Q_one_le_normalizer_Q_inf_Q_one Y (j := 0)
      (by simpa using (Y.Q_le_Gi_adj 1).trans inf_le_left)
  have hQ1NB : Y.Q 1 ≤ Subgroup.normalizer ((Y.Q 2 ⊓ Y.Q 1 : Subgroup G) : Set G) :=
    Q_one_le_normalizer_Q_inf_Q_one Y (j := 2)
      (by simpa using (Y.Q_le_Gi_adj 1).trans inf_le_right)
  have hAB : ⁅Y.Q 0 ⊓ Y.Q 1, Y.Q 2 ⊓ Y.Q 1⁆ ≤ Y.Z 1 :=
    (le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((inf_le_right : Y.Q 2 ⊓ Y.Q 1 ≤ Y.Q 1).trans hQ1NA))
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        ((inf_le_right : Y.Q 0 ⊓ Y.Q 1 ≤ Y.Q 1).trans hQ1NB))).trans
      ((inf_le_inf inf_le_left inf_le_left).trans (caseC_n Y H hZ h5).2.2.2.le)
  exact ⟨Y.Z_le_Q 1, commutator_self_Q_one_le_Z_one Y H hZ hderQ0 hAB,
    by simpa [pow_two] using mul_self_mem_Z_one Y H hZ hAB⟩

private noncomputable def nbrCore (Y : Setup Γ G) (v : V) : Subgroup G :=
  pCoreOf 2 (MulAction.stabilizer G v) ⊓ Y.Q 1

private theorem nbrCore_vert (Y : Setup Γ G) (i : ℤ) :
    nbrCore Y (Y.vert i) = Y.Q i ⊓ Y.Q 1 := rfl

private theorem nbrCore_le_Q_one (Y : Setup Γ G) (v : V) : nbrCore Y v ≤ Y.Q 1 :=
  inf_le_right

private theorem nbrCore_smul (Y : Setup Γ G) {g : G} (hg : g ∈ Y.Gi 1) (v : V) :
    conjSub g (nbrCore Y v) = nbrCore Y (g • v) := by
  have hg1 : g • Y.vert 1 = Y.vert 1 :=
    MulAction.mem_stabilizer_iff.mp hg
  have hQ : conjSub g (Y.Q 1) = Y.Q 1 := (Y.Q_smul Y hg1).symm
  calc conjSub g (nbrCore Y v)
      = conjSub g (pCoreOf 2 (MulAction.stabilizer G v)) ⊓ conjSub g (Y.Q 1) := by
        rw [nbrCore, conjSub_inf]
    _ = pCoreOf 2 (conjSub g (MulAction.stabilizer G v)) ⊓ Y.Q 1 := by
        rw [← pCoreOf_conjSub, hQ]
    _ = pCoreOf 2 (MulAction.stabilizer G (g • v)) ⊓ Y.Q 1 := by
        rw [stabilizer_smul_eq_conjSub]
    _ = nbrCore Y (g • v) := rfl

private theorem adj_one_iff (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {x : V}
    (hx1 : Γ.Adj (Y.vert 1) x) (hx0 : x ≠ Y.vert 0) (hx2 : x ≠ Y.vert 2) :
    ∀ w : V, Γ.Adj (Y.vert 1) w ↔ w = Y.vert 0 ∨ w = Y.vert 2 ∨ w = x := by
  intro w
  rw [← SimpleGraph.mem_neighborSet, neighborSet_one_eq Y H hx1 hx0 hx2]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

private theorem smul_third_eq_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {x : V}
    (hx1 : Γ.Adj (Y.vert 1) x) (hx0 : x ≠ Y.vert 0) (hx2 : x ≠ Y.vert 2) {g : G}
    (hg : g ∈ Y.Gi 1) (hg0 : g • Y.vert 0 = x) (hg2 : g • Y.vert 2 = Y.vert 0) :
    g • x = Y.vert 2 := by
  have hg1 : g • Y.vert 1 = Y.vert 1 := MulAction.mem_stabilizer_iff.mp hg
  have hnbr : Γ.Adj (Y.vert 1) (g • x) := by
    have h := (Y.hyp.adj_smul g (Y.vert 1) x).mpr hx1
    rwa [hg1] at h
  have hne0 : g • x ≠ Y.vert 0 := by
    intro h
    have h' : x = Y.vert 2 := MulAction.injective g (h.trans hg2.symm)
    exact hx2 h'
  have hnex : g • x ≠ x := by
    intro h
    have h' : x = Y.vert 0 := MulAction.injective g (h.trans hg0.symm)
    exact hx0 h'
  rcases (adj_one_iff Y H hx1 hx0 hx2 (g • x)).mp hnbr with h | h | h
  · exact absurd h hne0
  · exact h
  · exact absurd h hnex

private theorem smul_third_eq_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {x : V}
    (hx1 : Γ.Adj (Y.vert 1) x) (hx0 : x ≠ Y.vert 0) (hx2 : x ≠ Y.vert 2) {g : G}
    (hg : g ∈ Y.Gi 1) (hg2 : g • Y.vert 2 = x) (hg0 : g • Y.vert 0 = Y.vert 2) :
    g • x = Y.vert 0 := by
  have hg1 : g • Y.vert 1 = Y.vert 1 := MulAction.mem_stabilizer_iff.mp hg
  have hnbr : Γ.Adj (Y.vert 1) (g • x) := by
    have h := (Y.hyp.adj_smul g (Y.vert 1) x).mpr hx1
    rwa [hg1] at h
  have hne2 : g • x ≠ Y.vert 2 := by
    intro h
    have h' : x = Y.vert 0 := MulAction.injective g (h.trans hg0.symm)
    exact hx0 h'
  have hnex : g • x ≠ x := by
    intro h
    have h' : x = Y.vert 2 := MulAction.injective g (h.trans hg2.symm)
    exact hx2 h'
  rcases (adj_one_iff Y H hx1 hx0 hx2 (g • x)).mp hnbr with h | h | h
  · exact h
  · exact absurd h hne2
  · exact absurd h hnex

private theorem exists_order_three_K (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (h5 : s = 5) : ∃ k ∈ Y.K, orderOf k = 3 :=
  Y.exists_orderOf_three_K H (caseC_n Y H hZ h5).1

private def relSet (Q H : Subgroup G) : Set ↥Q := {y | (y : G) ∈ H}

private theorem ncard_relSet {Q H : Subgroup G} [Finite ↥Q] :
    (relSet Q H).ncard = Nat.card ↥(H ⊓ Q) := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr ?_
  exact
    { toFun := fun y => ⟨(y.1 : G), ⟨y.2, y.1.2⟩⟩
      invFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }

private theorem relSet_inf (Q H K : Subgroup G) :
    relSet Q H ∩ relSet Q K = relSet Q (H ⊓ K) := by
  ext y
  simp [relSet, Subgroup.mem_inf]

private theorem ncard_relSet_bot (Q : Subgroup G) [Finite ↥Q] :
    (relSet Q (⊥ : Subgroup G)).ncard = 1 := by
  rw [ncard_relSet]
  simp

private noncomputable def conjOnQ (Y : Setup Γ G) {g : G} (hg : g ∈ Y.Gi 1) :
    ↥(Y.Q 1) → ↥(Y.Q 1) :=
  fun y => ⟨g * (y : G) * g⁻¹, by
    have hg1 : g • Y.vert 1 = Y.vert 1 := MulAction.mem_stabilizer_iff.mp hg
    have hQ : conjSub g (Y.Q 1) = Y.Q 1 := (Y.Q_smul Y hg1).symm
    have hy : g * (y : G) * g⁻¹ ∈ conjSub g (Y.Q 1) := mul_mem_conjSub y.2
    rwa [hQ] at hy⟩

private theorem conjOnQ_apply (Y : Setup Γ G) {g : G} (hg : g ∈ Y.Gi 1) (y : ↥(Y.Q 1)) :
    (conjOnQ Y hg y : G) = g * (y : G) * g⁻¹ := rfl

private theorem conjOnQ_injective (Y : Setup Γ G) {g : G} (hg : g ∈ Y.Gi 1) :
    Function.Injective (conjOnQ Y hg) := by
  intro y z h
  apply Subtype.ext
  have h' : g * (y : G) * g⁻¹ = g * (z : G) * g⁻¹ := by
    simpa only [conjOnQ_apply] using congrArg Subtype.val h
  exact mul_left_cancel (mul_right_cancel h')

private theorem conjOnQ_mem_nbrCore_iff (Y : Setup Γ G) {g : G} (hg : g ∈ Y.Gi 1)
    (y : ↥(Y.Q 1)) (w : V) :
    ((conjOnQ Y hg y : G) ∈ nbrCore Y w) ↔ ((y : G) ∈ nbrCore Y (g⁻¹ • w)) := by
  have h := nbrCore_smul Y hg (g⁻¹ • w)
  rw [smul_inv_smul] at h
  rw [← h, mem_conjSub]
  have hc : g⁻¹ * (conjOnQ Y hg y : G) * g = (y : G) := by
    rw [conjOnQ_apply]
    group
  rw [hc]

private theorem conjOnQ_sq_mem (Y : Setup Γ G) {g : G} (hg : g ∈ Y.Gi 1)
    {v w : V} (hvw : g • v = w) (y : ↥(Y.Q 1)) :
    ((conjOnQ Y hg y : G) ^ 2 ∈ vertZ (G := G) w) ↔
      ((y : G) ^ 2 ∈ vertZ (G := G) v) := by
  have hsq : ((conjOnQ Y hg y : G) ^ 2) = g * ((y : G) ^ 2) * g⁻¹ := by
    rw [conjOnQ_apply, pow_two, pow_two]
    group
  rw [hsq]
  have hZ : vertZ (G := G) w = conjSub g (vertZ (G := G) v) := by
    rw [← hvw]
    exact vertZ_smul (G := G) g v
  rw [hZ, mem_conjSub]
  have hc : g⁻¹ * (g * (y : G) ^ 2 * g⁻¹) * g = (y : G) ^ 2 := by group
  rw [hc]

private def Mset (Y : Setup Γ G) (x : V) : Set ↥(Y.Q 1) :=
  {y | (y : G) ∉ Y.Q 0 ∧ (y : G) ∉ Y.Q 2 ∧ (y : G) ∉ nbrCore Y x}

private theorem mem_Q_zero_iff (Y : Setup Γ G) (y : ↥(Y.Q 1)) :
    (y : G) ∈ Y.Q 0 ↔ (y : G) ∈ nbrCore Y (Y.vert 0) := by
  rw [nbrCore_vert]
  exact ⟨fun h => Subgroup.mem_inf.mpr ⟨h, y.2⟩, fun h => (Subgroup.mem_inf.mp h).1⟩

private theorem mem_Q_two_iff (Y : Setup Γ G) (y : ↥(Y.Q 1)) :
    (y : G) ∈ Y.Q 2 ↔ (y : G) ∈ nbrCore Y (Y.vert 2) := by
  rw [nbrCore_vert]
  exact ⟨fun h => Subgroup.mem_inf.mpr ⟨h, y.2⟩, fun h => (Subgroup.mem_inf.mp h).1⟩

private theorem ncard_three_nbr (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {x : V}
    (hx1 : Γ.Adj (Y.vert 1) x) (hx0 : x ≠ Y.vert 0) (hx2 : x ≠ Y.vert 2) :
    ({Y.vert 0, Y.vert 2, x} : Set V).ncard = 3 := by
  rw [← neighborSet_one_eq Y H hx1 hx0 hx2]
  exact ncard_neighborSet_one Y H

private theorem smul_nbr_set (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {x : V}
    (hx1 : Γ.Adj (Y.vert 1) x) (hx0 : x ≠ Y.vert 0) (hx2 : x ≠ Y.vert 2)
    {g : G} (hg : g ∈ Y.Gi 1) :
    ({g • Y.vert 0, g • Y.vert 2, g • x} : Set V) = {Y.vert 0, Y.vert 2, x} := by
  have hg1 : g • Y.vert 1 = Y.vert 1 := MulAction.mem_stabilizer_iff.mp hg
  have hnbr := adj_one_iff Y H hx1 hx0 hx2
  have hsub : ({g • Y.vert 0, g • Y.vert 2, g • x} : Set V) ⊆
      ({Y.vert 0, Y.vert 2, x} : Set V) := by
    intro w hw
    rcases (by simpa using hw) with rfl | rfl | rfl
    · have h : Γ.Adj (Y.vert 1) (g • Y.vert 0) := by
        have h' := (Y.hyp.adj_smul g (Y.vert 1) (Y.vert 0)).mpr ((Y.adj 0).symm)
        rwa [hg1] at h'
      exact (hnbr (g • Y.vert 0)).mp h
    · have h : Γ.Adj (Y.vert 1) (g • Y.vert 2) := by
        have h' := (Y.hyp.adj_smul g (Y.vert 1) (Y.vert 2)).mpr (Y.adj 1)
        rwa [hg1] at h'
      exact (hnbr (g • Y.vert 2)).mp h
    · have h : Γ.Adj (Y.vert 1) (g • x) := by
        have h' := (Y.hyp.adj_smul g (Y.vert 1) x).mpr hx1
        rwa [hg1] at h'
      exact (hnbr (g • x)).mp h
  have hsrc : ({g • Y.vert 0, g • Y.vert 2, g • x} : Set V).ncard = 3 := by
    have himg : ({g • Y.vert 0, g • Y.vert 2, g • x} : Set V) =
        (fun v => g • v) '' ({Y.vert 0, Y.vert 2, x} : Set V) := by
      simp
    rw [himg, Set.ncard_image_of_injective _ (MulAction.injective g),
      ncard_three_nbr Y H hx1 hx0 hx2]
  exact Set.eq_of_subset_of_ncard_le hsub
    (by rw [ncard_three_nbr Y H hx1 hx0 hx2, hsrc]) (by toFinite_tac)

private theorem conjOnQ_mem_Mset_iff (Y : Setup Γ G) {x : V} {g : G} (hg : g ∈ Y.Gi 1)
    (y : ↥(Y.Q 1))
    (hpre : ({g⁻¹ • Y.vert 0, g⁻¹ • Y.vert 2, g⁻¹ • x} : Set V) =
      ({Y.vert 0, Y.vert 2, x} : Set V)) :
    conjOnQ Y hg y ∈ Mset Y x ↔ y ∈ Mset Y x := by
  have hA0 (u : ↥(Y.Q 1)) : (u : G) ∉ Y.Q 0 ↔ (u : G) ∉ nbrCore Y (Y.vert 0) :=
    not_congr (mem_Q_zero_iff Y u)
  have hA2 (u : ↥(Y.Q 1)) : (u : G) ∉ Y.Q 2 ↔ (u : G) ∉ nbrCore Y (Y.vert 2) :=
    not_congr (mem_Q_two_iff Y u)
  simp only [Mset, Set.mem_setOf_eq, hA0, hA2]
  rw [conjOnQ_mem_nbrCore_iff Y hg y (Y.vert 0),
    conjOnQ_mem_nbrCore_iff Y hg y (Y.vert 2),
    conjOnQ_mem_nbrCore_iff Y hg y x]
  have h := congrArg (fun S : Set V => ∀ v ∈ S, (y : G) ∉ nbrCore Y v) hpre
  simpa only [Set.forall_mem_insert, Set.forall_mem_singleton, eq_iff_iff] using h

private theorem nbrCore_inter_transport (Y : Setup Γ G) {g : G} (hg : g ∈ Y.Gi 1)
    {v w a b : V} (hv : g • v = a) (hw : g • w = b)
    (h : nbrCore Y v ⊓ nbrCore Y w = Y.Z 1) :
    nbrCore Y a ⊓ nbrCore Y b = Y.Z 1 := by
  have hconj : conjSub g (nbrCore Y v ⊓ nbrCore Y w) = nbrCore Y a ⊓ nbrCore Y b := by
    rw [conjSub_inf, nbrCore_smul Y hg v, nbrCore_smul Y hg w, hv, hw]
  rw [h, Y.Z_normal 1 g hg] at hconj
  exact hconj.symm

private theorem vertZ_inter_transport {g : G}
    {v w a b : V} (hv : g • v = a) (hw : g • w = b)
    (h : vertZ (G := G) v ⊓ vertZ (G := G) w = ⊥) :
    vertZ (G := G) a ⊓ vertZ (G := G) b = ⊥ := by
  have hconj : conjSub g (vertZ (G := G) v ⊓ vertZ (G := G) w) =
      vertZ (G := G) a ⊓ vertZ (G := G) b := by
    rw [conjSub_inf, ← vertZ_smul (G := G) g v, ← vertZ_smul (G := G) g w, hv, hw]
  rw [h] at hconj
  simp only [conjSub_bot] at hconj
  exact hconj.symm

private theorem nbrCore_zero_inf_nbrCore_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (h5 : s = 5) :
    nbrCore Y (Y.vert 0) ⊓ nbrCore Y (Y.vert 2) = Y.Z 1 := by
  have hQ02eq : Y.Q 0 ⊓ Y.Q 2 = Y.Z 1 := (caseC_n Y H hZ h5).2.2.2
  have hZ1leQ0 : Y.Z 1 ≤ Y.Q 0 := by rw [← hQ02eq]; exact inf_le_left
  have hZ1leQ2 : Y.Z 1 ≤ Y.Q 2 := by rw [← hQ02eq]; exact inf_le_right
  have hZ1leQ1 : Y.Z 1 ≤ Y.Q 1 := Y.Z_le_Q 1
  rw [nbrCore_vert, nbrCore_vert]
  refine le_antisymm ?_ ?_
  · intro y hy
    rcases Subgroup.mem_inf.mp hy with ⟨hyL, hyR⟩
    rcases Subgroup.mem_inf.mp hyL with ⟨hy0, -⟩
    rcases Subgroup.mem_inf.mp hyR with ⟨hy2, -⟩
    rw [← hQ02eq]
    exact Subgroup.mem_inf.mpr ⟨hy0, hy2⟩
  · intro y hy
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr ⟨hZ1leQ0 hy, hZ1leQ1 hy⟩,
       Subgroup.mem_inf.mpr ⟨hZ1leQ2 hy, hZ1leQ1 hy⟩⟩

private theorem card_nbrCore_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) : Nat.card ↥(nbrCore Y (Y.vert 0)) = 16 := by
  haveI : Finite ↥(Y.Q 1) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  have hA02 : nbrCore Y (Y.vert 0) ⊓ nbrCore Y (Y.vert 2) = Y.Z 1 :=
    nbrCore_zero_inf_nbrCore_two Y H hZ h5
  have hQ1G2 : Y.Q 1 ≤ Y.Gi 2 := by
    simpa using (Y.Q_le_Gi_adj 1).trans inf_le_right
  have hQ1NA2 : Y.Q 1 ≤ Subgroup.normalizer ((nbrCore Y (Y.vert 2) : Subgroup G) : Set G) := by
    rw [nbrCore_vert]
    exact Q_one_le_normalizer_Q_inf_Q_one Y hQ1G2
  have hA2norm : ((nbrCore Y (Y.vert 2)).subgroupOf (Y.Q 1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (nbrCore_le_Q_one Y (Y.vert 2))).mpr hQ1NA2
  have hsupA : nbrCore Y (Y.vert 0) ⊔ nbrCore Y (Y.vert 2) = Y.Q 1 := by
    rw [nbrCore_vert, nbrCore_vert]
    exact (Q_eq_sup_inf Y H 1).symm
  have hprod := card_sup_mul_card_inf_of_le_normal
    (H := nbrCore Y (Y.vert 0)) (K := nbrCore Y (Y.vert 2)) (L := Y.Q 1)
    (nbrCore_le_Q_one Y (Y.vert 0)) (nbrCore_le_Q_one Y (Y.vert 2)) hA2norm
  rw [hsupA, hA02, card_Q_one_of_caseC Y H hZ h5,
    (s52_step8_Z Y H hZ 1 (by norm_num)).2,
    show (2 : ℕ) ^ 6 * 4 = 256 by norm_num] at hprod
  obtain ⟨a, haL, ha0⟩ := (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).trans (Y.vert 0) (Y.vert 2)
    ((Y.adj 0).symm) (Y.adj 1)
  have hcardA0A2 : Nat.card ↥(nbrCore Y (Y.vert 0)) =
      Nat.card ↥(nbrCore Y (Y.vert 2)) := by
    have hA2eq : nbrCore Y (Y.vert 2) = conjSub a (nbrCore Y (Y.vert 0)) := by
      have h := nbrCore_smul Y (Y.L_le_Gi 1 haL) (Y.vert 0)
      rw [ha0] at h
      exact h.symm
    rw [hA2eq, card_conjSub]
  have hsq : Nat.card ↥(nbrCore Y (Y.vert 0)) *
      Nat.card ↥(nbrCore Y (Y.vert 0)) = 256 := by
    rw [← hcardA0A2] at hprod
    exact hprod.symm
  nlinarith

private theorem card_nbrCore_of_adj (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) {v : V} (hv : Γ.Adj (Y.vert 1) v) :
    Nat.card ↥(nbrCore Y v) = 16 := by
  obtain ⟨g, hgL, hg0⟩ := (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).trans (Y.vert 0) v
    ((Y.adj 0).symm) hv
  have h := nbrCore_smul Y (Y.L_le_Gi 1 hgL) (Y.vert 0)
  rw [hg0] at h
  rw [← h, card_conjSub, card_nbrCore_zero Y H hZ h5]

private theorem vertZ_third_le_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {x : V} (hx1 : Γ.Adj (Y.vert 1) x) : vertZ (G := G) x ≤ Y.Z 1 := by
  obtain ⟨b, hbL, hb0⟩ := (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).trans (Y.vert 0) x
    ((Y.adj 0).symm) hx1
  have hZ1eq : Y.Z 1 = Y.Z 0 ⊔ Y.Z 2 := (s52_step8 Y H hZ).2.2.2.2.1
  have hZ0leZ1 : Y.Z 0 ≤ Y.Z 1 := by rw [hZ1eq]; exact le_sup_left
  have hZxeq : vertZ (G := G) x = conjSub b (Y.Z 0) := by
    have h := vertZ_smul (G := G) b (Y.vert 0)
    rw [hb0] at h
    exact h
  rw [hZxeq]
  exact (conjSub_mono b hZ0leZ1).trans (le_of_eq (Y.Z_normal 1 b (Y.L_le_Gi 1 hbL)))

private theorem card_vertZ_third (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {x : V} (hx1 : Γ.Adj (Y.vert 1) x) : Nat.card ↥(vertZ (G := G) x) = 2 := by
  obtain ⟨b, hbL, hb0⟩ := (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).trans (Y.vert 0) x
    ((Y.adj 0).symm) hx1
  have hZ0card : Nat.card ↥(Y.Z 0) = 2 := (s52_step8 Y H hZ).2.2.2.2.2.2.1
  have hZxeq : vertZ (G := G) x = conjSub b (Y.Z 0) := by
    have h := vertZ_smul (G := G) b (Y.vert 0)
    rw [hb0] at h
    exact h
  rw [hZxeq, card_conjSub, hZ0card]

private theorem third_inf_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) {x : V} (hx1 : Γ.Adj (Y.vert 1) x) (hx0 : x ≠ Y.vert 0)
    (hx2 : x ≠ Y.vert 2) :
    nbrCore Y x ⊓ nbrCore Y (Y.vert 2) = Y.Z 1 ∧ vertZ (G := G) x ⊓ Y.Z 2 = ⊥ := by
  have hA02 : nbrCore Y (Y.vert 0) ⊓ nbrCore Y (Y.vert 2) = Y.Z 1 :=
    nbrCore_zero_inf_nbrCore_two Y H hZ h5
  have hZ02bot : Y.Z 0 ⊓ Y.Z 2 = ⊥ := (s52_step8 Y H hZ).2.2.2.2.2.1
  obtain ⟨b, hbL, hb0⟩ := (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).trans (Y.vert 0) x
    ((Y.adj 0).symm) hx1
  have hnbr := adj_one_iff Y H hx1 hx0 hx2
  have hb2nbr : Γ.Adj (Y.vert 1) (b • Y.vert 2) := by
    have h := (Y.hyp.adj_smul b (Y.vert 1) (Y.vert 2)).mpr (Y.adj 1)
    rwa [MulAction.mem_stabilizer_iff.mp (Y.L_le_Gi 1 hbL)] at h
  have hb2ne : b • Y.vert 2 ≠ x := by
    intro h
    have h' : Y.vert 2 = Y.vert 0 := MulAction.injective b (h.trans hb0.symm)
    have := Y.vert_injective h'
    omega
  have hb2cases : b • Y.vert 2 = Y.vert 0 ∨ b • Y.vert 2 = Y.vert 2 := by
    rcases (hnbr (b • Y.vert 2)).mp hb2nbr with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hb2ne
  constructor
  · rcases hb2cases with hb2 | hb2
    · have hbx : b • x = Y.vert 2 := smul_third_eq_two Y H hx1 hx0 hx2
        (Y.L_le_Gi 1 hbL) hb0 hb2
      have hb20 : b ^ 2 • Y.vert 0 = Y.vert 2 := by
        rw [pow_two, mul_smul, hb0, hbx]
      have hb22 : b ^ 2 • Y.vert 2 = x := by
        rw [pow_two, mul_smul, hb2, hb0]
      have h := nbrCore_inter_transport Y (g := b ^ 2)
        (Y.L_le_Gi 1 ((Y.L 1).pow_mem hbL 2)) hb20 hb22 hA02
      simpa [inf_comm] using h
    · exact nbrCore_inter_transport Y (g := b) (Y.L_le_Gi 1 hbL) hb0 hb2 hA02
  · rw [Setup.Z_eq_vertZ]
    rcases hb2cases with hb2 | hb2
    · have hbx : b • x = Y.vert 2 := smul_third_eq_two Y H hx1 hx0 hx2
        (Y.L_le_Gi 1 hbL) hb0 hb2
      have hb20 : b ^ 2 • Y.vert 0 = Y.vert 2 := by
        rw [pow_two, mul_smul, hb0, hbx]
      have hb22 : b ^ 2 • Y.vert 2 = x := by
        rw [pow_two, mul_smul, hb2, hb0]
      have h := vertZ_inter_transport (g := b ^ 2) hb20 hb22 hZ02bot
      simpa [inf_comm] using h
    · exact vertZ_inter_transport (g := b) hb0 hb2 hZ02bot

private theorem third_inf_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) {x : V} (hx1 : Γ.Adj (Y.vert 1) x) (hx0 : x ≠ Y.vert 0)
    (hx2 : x ≠ Y.vert 2) :
    nbrCore Y x ⊓ nbrCore Y (Y.vert 0) = Y.Z 1 ∧ vertZ (G := G) x ⊓ Y.Z 0 = ⊥ := by
  have hA02 : nbrCore Y (Y.vert 0) ⊓ nbrCore Y (Y.vert 2) = Y.Z 1 :=
    nbrCore_zero_inf_nbrCore_two Y H hZ h5
  have hZ02bot : Y.Z 0 ⊓ Y.Z 2 = ⊥ := (s52_step8 Y H hZ).2.2.2.2.2.1
  obtain ⟨c, hcL, hc2⟩ := (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).trans (Y.vert 2) x
    (Y.adj 1) hx1
  have hnbr := adj_one_iff Y H hx1 hx0 hx2
  have hc0nbr : Γ.Adj (Y.vert 1) (c • Y.vert 0) := by
    have h := (Y.hyp.adj_smul c (Y.vert 1) (Y.vert 0)).mpr ((Y.adj 0).symm)
    rwa [MulAction.mem_stabilizer_iff.mp (Y.L_le_Gi 1 hcL)] at h
  have hc0ne : c • Y.vert 0 ≠ x := by
    intro h
    have h' : Y.vert 0 = Y.vert 2 := MulAction.injective c (h.trans hc2.symm)
    have := Y.vert_injective h'
    omega
  have hc0cases : c • Y.vert 0 = Y.vert 0 ∨ c • Y.vert 0 = Y.vert 2 := by
    rcases (hnbr (c • Y.vert 0)).mp hc0nbr with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hc0ne
  constructor
  · rcases hc0cases with hc0 | hc0
    · exact nbrCore_inter_transport Y (g := c) (Y.L_le_Gi 1 hcL) hc2 hc0
        (by rw [inf_comm]; exact hA02)
    · have hcx : c • x = Y.vert 0 := smul_third_eq_zero Y H hx1 hx0 hx2
        (Y.L_le_Gi 1 hcL) hc2 hc0
      have hc20 : c ^ 2 • Y.vert 0 = x := by
        rw [pow_two, mul_smul, hc0, hc2]
      have hc22 : c ^ 2 • Y.vert 2 = Y.vert 0 := by
        rw [pow_two, mul_smul, hc2, hcx]
      exact nbrCore_inter_transport Y (g := c ^ 2)
        (Y.L_le_Gi 1 ((Y.L 1).pow_mem hcL 2)) hc20 hc22 hA02
  · rw [Setup.Z_eq_vertZ]
    rcases hc0cases with hc0 | hc0
    · exact vertZ_inter_transport (g := c) hc2 hc0 (by rw [inf_comm]; exact hZ02bot)
    · have hcx : c • x = Y.vert 0 := smul_third_eq_zero Y H hx1 hx0 hx2
        (Y.L_le_Gi 1 hcL) hc2 hc0
      have hc20 : c ^ 2 • Y.vert 0 = x := by
        rw [pow_two, mul_smul, hc0, hc2]
      have hc22 : c ^ 2 • Y.vert 2 = Y.vert 0 := by
        rw [pow_two, mul_smul, hc2, hcx]
      exact vertZ_inter_transport (g := c ^ 2) hc20 hc22 hZ02bot

private theorem ncard_Mset (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) {x : V} (hx1 : Γ.Adj (Y.vert 1) x) (hx0 : x ≠ Y.vert 0)
    (hx2 : x ≠ Y.vert 2) : (Mset Y x).ncard = 24 := by
  have hQfin : Finite ↥(Y.Q 1) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  haveI := hQfin
  have hQcard : Nat.card ↥(Y.Q 1) = 64 := by
    rw [card_Q_one_of_caseC Y H hZ h5]
    norm_num
  have hQ02eq : Y.Q 0 ⊓ Y.Q 2 = Y.Z 1 := (caseC_n Y H hZ h5).2.2.2
  have hZ1card : Nat.card ↥(Y.Z 1) = 4 := (s52_step8_Z Y H hZ 1 (by norm_num)).2
  have hZ1leQ1 : Y.Z 1 ≤ Y.Q 1 := Y.Z_le_Q 1
  have hAxA2 : nbrCore Y x ⊓ nbrCore Y (Y.vert 2) = Y.Z 1 :=
    (third_inf_two Y H hZ h5 hx1 hx0 hx2).1
  have hAxA0 : nbrCore Y x ⊓ nbrCore Y (Y.vert 0) = Y.Z 1 :=
    (third_inf_zero Y H hZ h5 hx1 hx0 hx2).1
  have hZxleQ1 : vertZ (G := G) x ≤ Y.Q 1 :=
    (vertZ_third_le_Z_one Y H hZ hx1).trans hZ1leQ1
  have hZxcard : Nat.card ↥(vertZ (G := G) x) = 2 := card_vertZ_third Y H hZ hx1
  have hcardAx : Nat.card ↥(nbrCore Y x) = 16 := card_nbrCore_of_adj Y H hZ h5 hx1
  have hcardA0 : Nat.card ↥(nbrCore Y (Y.vert 0)) = 16 := card_nbrCore_zero Y H hZ h5
  have hQ0Ax : Y.Q 0 ⊓ nbrCore Y x = Y.Z 1 := by
    calc Y.Q 0 ⊓ nbrCore Y x
        = Y.Q 0 ⊓ (Y.Q 1 ⊓ nbrCore Y x) := by
          rw [inf_eq_right.mpr (nbrCore_le_Q_one Y x)]
      _ = (Y.Q 0 ⊓ Y.Q 1) ⊓ nbrCore Y x := by rw [inf_assoc]
      _ = nbrCore Y (Y.vert 0) ⊓ nbrCore Y x := by rw [nbrCore_vert]
      _ = Y.Z 1 := by rw [inf_comm]; exact hAxA0
  have hQ2Ax : Y.Q 2 ⊓ nbrCore Y x = Y.Z 1 := by
    calc Y.Q 2 ⊓ nbrCore Y x
        = Y.Q 2 ⊓ (Y.Q 1 ⊓ nbrCore Y x) := by
          rw [inf_eq_right.mpr (nbrCore_le_Q_one Y x)]
      _ = (Y.Q 2 ⊓ Y.Q 1) ⊓ nbrCore Y x := by rw [inf_assoc]
      _ = nbrCore Y (Y.vert 2) ⊓ nbrCore Y x := by rw [nbrCore_vert]
      _ = Y.Z 1 := by rw [inf_comm]; exact hAxA2
  have hZ1leAx : Y.Z 1 ≤ nbrCore Y x := by
    rw [← hQ0Ax]
    exact inf_le_right
  have hU0card : (relSet (Y.Q 1) (Y.Q 0)).ncard = 16 := by
    rw [ncard_relSet, ← nbrCore_vert Y 0, hcardA0]
  have hU2card : (relSet (Y.Q 1) (Y.Q 2)).ncard = 16 := by
    rw [ncard_relSet]
    exact card_nbrCore_of_adj Y H hZ h5 (Y.adj 1)
  have hUxcard : (relSet (Y.Q 1) (nbrCore Y x)).ncard = 16 := by
    rw [ncard_relSet, inf_eq_left.mpr (nbrCore_le_Q_one Y x), hcardAx]
  have hU02card : (relSet (Y.Q 1) (Y.Q 0) ∩ relSet (Y.Q 1) (Y.Q 2)).ncard = 4 := by
    rw [relSet_inf, hQ02eq, ncard_relSet, inf_eq_left.mpr hZ1leQ1, hZ1card]
  have hU0xcard : (relSet (Y.Q 1) (Y.Q 0) ∩ relSet (Y.Q 1) (nbrCore Y x)).ncard = 4 := by
    rw [relSet_inf, hQ0Ax, ncard_relSet, inf_eq_left.mpr hZ1leQ1, hZ1card]
  have hU2xcard : (relSet (Y.Q 1) (Y.Q 2) ∩ relSet (Y.Q 1) (nbrCore Y x)).ncard = 4 := by
    rw [relSet_inf, hQ2Ax, ncard_relSet, inf_eq_left.mpr hZ1leQ1, hZ1card]
  have hU02union : ((relSet (Y.Q 1) (Y.Q 0) ∪ relSet (Y.Q 1) (Y.Q 2))).ncard = 28 := by
    have h := Set.ncard_union_add_ncard_inter
      (relSet (Y.Q 1) (Y.Q 0)) (relSet (Y.Q 1) (Y.Q 2))
    rw [hU0card, hU2card, hU02card] at h
    omega
  have hinter : (((relSet (Y.Q 1) (Y.Q 0) ∪ relSet (Y.Q 1) (Y.Q 2)) ∩
      relSet (Y.Q 1) (nbrCore Y x))).ncard = 4 := by
    rw [Set.union_inter_distrib_right]
    have h := Set.ncard_union_add_ncard_inter
      (relSet (Y.Q 1) (Y.Q 0) ∩ relSet (Y.Q 1) (nbrCore Y x))
      (relSet (Y.Q 1) (Y.Q 2) ∩ relSet (Y.Q 1) (nbrCore Y x))
    have htriple : ((relSet (Y.Q 1) (Y.Q 0) ∩ relSet (Y.Q 1) (nbrCore Y x)) ∩
        (relSet (Y.Q 1) (Y.Q 2) ∩ relSet (Y.Q 1) (nbrCore Y x))).ncard = 4 := by
      have heq : ((relSet (Y.Q 1) (Y.Q 0) ∩ relSet (Y.Q 1) (nbrCore Y x)) ∩
          (relSet (Y.Q 1) (Y.Q 2) ∩ relSet (Y.Q 1) (nbrCore Y x))) =
          relSet (Y.Q 1) (Y.Q 0) ∩ relSet (Y.Q 1) (Y.Q 2) := by
        ext y
        constructor
        · rintro ⟨⟨hy0, -⟩, ⟨hy2, -⟩⟩
          exact ⟨hy0, hy2⟩
        · intro hy
          have hyZ : (y : G) ∈ Y.Z 1 := by
            rw [← hQ02eq]
            exact Subgroup.mem_inf.mpr ⟨hy.1, hy.2⟩
          exact ⟨⟨hy.1, hZ1leAx hyZ⟩, ⟨hy.2, hZ1leAx hyZ⟩⟩
      rw [heq, hU02card]
    rw [hU0xcard, hU2xcard, htriple] at h
    omega
  let T : Set ↥(Y.Q 1) := (relSet (Y.Q 1) (Y.Q 0) ∪ relSet (Y.Q 1) (Y.Q 2)) ∪
    relSet (Y.Q 1) (nbrCore Y x)
  have hTcard : T.ncard = 40 := by
    have h := Set.ncard_union_add_ncard_inter
      (relSet (Y.Q 1) (Y.Q 0) ∪ relSet (Y.Q 1) (Y.Q 2))
      (relSet (Y.Q 1) (nbrCore Y x))
    rw [hU02union, hUxcard, hinter] at h
    dsimp [T]
    omega
  have hMeq : Mset Y x = Tᶜ := by
    ext y
    simp only [Mset, T, relSet, Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or]
    tauto
  rw [hMeq]
  have h := Set.ncard_compl (s := T) (α := ↥(Y.Q 1))
  rw [hQcard] at h
  omega

private theorem relSet_Z_one_eq_union (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) {x : V} (hx1 : Γ.Adj (Y.vert 1) x) (hx0 : x ≠ Y.vert 0)
    (hx2 : x ≠ Y.vert 2) :
    (relSet (Y.Q 1) (Y.Z 0) ∪ relSet (Y.Q 1) (Y.Z 2)) ∪
      relSet (Y.Q 1) (vertZ (G := G) x) = relSet (Y.Q 1) (Y.Z 1) := by
  haveI : Finite ↥(Y.Q 1) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  have hZ0card : Nat.card ↥(Y.Z 0) = 2 := (s52_step8 Y H hZ).2.2.2.2.2.2.1
  have hZ1card : Nat.card ↥(Y.Z 1) = 4 := (s52_step8_Z Y H hZ 1 (by norm_num)).2
  have hZ1eq : Y.Z 1 = Y.Z 0 ⊔ Y.Z 2 := (s52_step8 Y H hZ).2.2.2.2.1
  have hZ02bot : Y.Z 0 ⊓ Y.Z 2 = ⊥ := (s52_step8 Y H hZ).2.2.2.2.2.1
  have hZ0leQ1 : Y.Z 0 ≤ Y.Q 1 := (s52_step8 Y H hZ).2.2.2.1
  have hZ1leQ1 : Y.Z 1 ≤ Y.Q 1 := Y.Z_le_Q 1
  have hZ0leZ1 : Y.Z 0 ≤ Y.Z 1 := by rw [hZ1eq]; exact le_sup_left
  have hZ2leZ1 : Y.Z 2 ≤ Y.Z 1 := by rw [hZ1eq]; exact le_sup_right
  have hZ2leQ1 : Y.Z 2 ≤ Y.Q 1 := hZ2leZ1.trans hZ1leQ1
  have hZ2card : Nat.card ↥(Y.Z 2) = 2 := by
    rw [Z_two_eq_conj Y, card_conjSub, hZ0card]
  have hZxle : vertZ (G := G) x ≤ Y.Z 1 := vertZ_third_le_Z_one Y H hZ hx1
  have hZxleQ1 : vertZ (G := G) x ≤ Y.Q 1 := hZxle.trans hZ1leQ1
  have hZxcard : Nat.card ↥(vertZ (G := G) x) = 2 := card_vertZ_third Y H hZ hx1
  have hZxZ2 : vertZ (G := G) x ⊓ Y.Z 2 = ⊥ := (third_inf_two Y H hZ h5 hx1 hx0 hx2).2
  have hZxZ0 : vertZ (G := G) x ⊓ Y.Z 0 = ⊥ := (third_inf_zero Y H hZ h5 hx1 hx0 hx2).2
  have hZ1setcard : (relSet (Y.Q 1) (Y.Z 1)).ncard = 4 := by
    rw [ncard_relSet, inf_eq_left.mpr hZ1leQ1, hZ1card]
  have hZset0 : (relSet (Y.Q 1) (Y.Z 0)).ncard = 2 := by
    rw [ncard_relSet, inf_eq_left.mpr hZ0leQ1, hZ0card]
  have hZset2 : (relSet (Y.Q 1) (Y.Z 2)).ncard = 2 := by
    rw [ncard_relSet, inf_eq_left.mpr hZ2leQ1, hZ2card]
  have hZsetx : (relSet (Y.Q 1) (vertZ (G := G) x)).ncard = 2 := by
    rw [ncard_relSet, inf_eq_left.mpr hZxleQ1, hZxcard]
  have hZ02set : (relSet (Y.Q 1) (Y.Z 0) ∩ relSet (Y.Q 1) (Y.Z 2)).ncard = 1 := by
    rw [relSet_inf, hZ02bot, ncard_relSet_bot]
  have hZx2set : (relSet (Y.Q 1) (Y.Z 2) ∩ relSet (Y.Q 1) (vertZ (G := G) x)).ncard = 1 := by
    rw [relSet_inf, inf_comm, hZxZ2, ncard_relSet_bot]
  have hZx0set : (relSet (Y.Q 1) (Y.Z 0) ∩ relSet (Y.Q 1) (vertZ (G := G) x)).ncard = 1 := by
    rw [relSet_inf, inf_comm, hZxZ0, ncard_relSet_bot]
  have hZunioncard :
      (((relSet (Y.Q 1) (Y.Z 0) ∪ relSet (Y.Q 1) (Y.Z 2)) ∪
        relSet (Y.Q 1) (vertZ (G := G) x))).ncard = 4 := by
    have hU : ((relSet (Y.Q 1) (Y.Z 0) ∪ relSet (Y.Q 1) (Y.Z 2))).ncard = 3 := by
      have h := Set.ncard_union_add_ncard_inter
        (relSet (Y.Q 1) (Y.Z 0)) (relSet (Y.Q 1) (Y.Z 2))
      rw [hZset0, hZset2, hZ02set] at h
      omega
    have hPR : (((relSet (Y.Q 1) (Y.Z 0) ∩ relSet (Y.Q 1) (vertZ (G := G) x)) ∪
        (relSet (Y.Q 1) (Y.Z 2) ∩ relSet (Y.Q 1) (vertZ (G := G) x)))).ncard = 1 := by
      have htriple : (((relSet (Y.Q 1) (Y.Z 0) ∩ relSet (Y.Q 1) (vertZ (G := G) x)) ∩
          (relSet (Y.Q 1) (Y.Z 2) ∩ relSet (Y.Q 1) (vertZ (G := G) x)))).ncard = 1 := by
        have heq : (((relSet (Y.Q 1) (Y.Z 0) ∩ relSet (Y.Q 1) (vertZ (G := G) x)) ∩
            (relSet (Y.Q 1) (Y.Z 2) ∩ relSet (Y.Q 1) (vertZ (G := G) x)))) =
            relSet (Y.Q 1) (Y.Z 0) ∩ relSet (Y.Q 1) (Y.Z 2) := by
          ext y
          constructor
          · rintro ⟨⟨hy0, -⟩, ⟨hy2, -⟩⟩
            exact ⟨hy0, hy2⟩
          · intro hy
            have hybot : (y : G) ∈ Y.Z 0 ⊓ Y.Z 2 :=
              Subgroup.mem_inf.mpr ⟨hy.1, hy.2⟩
            rw [hZ02bot] at hybot
            have hy1 : (y : G) = 1 := Subgroup.mem_bot.mp hybot
            exact ⟨⟨hy.1, by simpa [relSet, hy1] using (vertZ (G := G) x).one_mem⟩,
              ⟨hy.2, by simpa [relSet, hy1] using (vertZ (G := G) x).one_mem⟩⟩
        rw [heq, hZ02set]
      have h := Set.ncard_union_add_ncard_inter
        (relSet (Y.Q 1) (Y.Z 0) ∩ relSet (Y.Q 1) (vertZ (G := G) x))
        (relSet (Y.Q 1) (Y.Z 2) ∩ relSet (Y.Q 1) (vertZ (G := G) x))
      rw [hZx0set, hZx2set, htriple] at h
      omega
    have h := Set.ncard_union_add_ncard_inter
      (relSet (Y.Q 1) (Y.Z 0) ∪ relSet (Y.Q 1) (Y.Z 2))
      (relSet (Y.Q 1) (vertZ (G := G) x))
    rw [hU, hZsetx, Set.union_inter_distrib_right, hPR] at h
    omega
  have hZunion_sub : ((relSet (Y.Q 1) (Y.Z 0) ∪ relSet (Y.Q 1) (Y.Z 2)) ∪
      relSet (Y.Q 1) (vertZ (G := G) x)) ⊆ relSet (Y.Q 1) (Y.Z 1) := by
    intro y hy
    rcases hy with (hy | hy) | hy
    · exact hZ0leZ1 hy
    · exact hZ2leZ1 hy
    · exact hZxle hy
  refine Set.eq_of_subset_of_ncard_le hZunion_sub ?_ (by toFinite_tac)
  rw [hZ1setcard, hZunioncard]

private theorem ncard_fibre_smul (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {x : V}
    (hx1 : Γ.Adj (Y.vert 1) x) (hx0 : x ≠ Y.vert 0) (hx2 : x ≠ Y.vert 2) {g : G}
    (hg : g ∈ Y.Gi 1) {v w : V} (hvw : g • v = w) :
    {y : ↥(Y.Q 1) | y ∈ Mset Y x ∧ (y : G) ^ 2 ∈ vertZ (G := G) w}.ncard =
    {y : ↥(Y.Q 1) | y ∈ Mset Y x ∧ (y : G) ^ 2 ∈ vertZ (G := G) v}.ncard := by
  haveI : Finite ↥(Y.Q 1) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  have hgInv : g⁻¹ ∈ Y.Gi 1 := (Y.Gi 1).inv_mem hg
  have hpre : ({g⁻¹ • Y.vert 0, g⁻¹ • Y.vert 2, g⁻¹ • x} : Set V) =
      {Y.vert 0, Y.vert 2, x} := smul_nbr_set Y H hx1 hx0 hx2 hgInv
  have hpreInv : ({(g⁻¹)⁻¹ • Y.vert 0, (g⁻¹)⁻¹ • Y.vert 2, (g⁻¹)⁻¹ • x} : Set V) =
      {Y.vert 0, Y.vert 2, x} := by
    simpa using smul_nbr_set Y H hx1 hx0 hx2 hg
  have hMmem : ∀ y : ↥(Y.Q 1), y ∈ Mset Y x → conjOnQ Y hg y ∈ Mset Y x := fun y hy =>
    (conjOnQ_mem_Mset_iff Y hg y hpre).mpr hy
  have hMinv : ∀ y : ↥(Y.Q 1), y ∈ Mset Y x → conjOnQ Y hgInv y ∈ Mset Y x := fun y hy =>
    (conjOnQ_mem_Mset_iff Y hgInv y hpreInv).mpr hy
  have hwv : g⁻¹ • w = v := by rw [← hvw]; exact inv_smul_smul g v
  refine le_antisymm ?_ ?_
  · refine Set.ncard_le_ncard_of_injOn
      (s := {y : ↥(Y.Q 1) | y ∈ Mset Y x ∧ (y : G) ^ 2 ∈ vertZ (G := G) w})
      (t := {y : ↥(Y.Q 1) | y ∈ Mset Y x ∧ (y : G) ^ 2 ∈ vertZ (G := G) v})
      (conjOnQ Y hgInv) ?_ ?_
    · intro z hz
      exact ⟨hMinv z hz.1, (conjOnQ_sq_mem Y hgInv hwv z).mpr hz.2⟩
    · intro y _ z _ h
      exact conjOnQ_injective Y hgInv h
  · refine Set.ncard_le_ncard_of_injOn
      (s := {y : ↥(Y.Q 1) | y ∈ Mset Y x ∧ (y : G) ^ 2 ∈ vertZ (G := G) v})
      (t := {y : ↥(Y.Q 1) | y ∈ Mset Y x ∧ (y : G) ^ 2 ∈ vertZ (G := G) w})
      (conjOnQ Y hg) ?_ ?_
    · intro z hz
      exact ⟨hMmem z hz.1, (conjOnQ_sq_mem Y hg hvw z).mpr hz.2⟩
    · intro y _ z _ h
      exact conjOnQ_injective Y hg h

private theorem ncard_Mset_eq_three_mul (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) {x : V} (hx1 : Γ.Adj (Y.vert 1) x) (hx0 : x ≠ Y.vert 0)
    (hx2 : x ≠ Y.vert 2) (hno : ∀ y ∈ Y.Q 1, y ∉ Y.Q 0 → y ^ 2 ≠ 1) :
    (Mset Y x).ncard =
      3 * {y : ↥(Y.Q 1) | y ∈ Mset Y x ∧
        (y : G) ^ 2 ∈ vertZ (G := G) (Y.vert 0)}.ncard := by
  haveI : Finite ↥(Y.Q 1) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  have hZ02bot : Y.Z 0 ⊓ Y.Z 2 = ⊥ := (s52_step8 Y H hZ).2.2.2.2.2.1
  have hZxZ2 : vertZ (G := G) x ⊓ Y.Z 2 = ⊥ := (third_inf_two Y H hZ h5 hx1 hx0 hx2).2
  have hZxZ0 : vertZ (G := G) x ⊓ Y.Z 0 = ⊥ := (third_inf_zero Y H hZ h5 hx1 hx0 hx2).2
  obtain ⟨a, haL, ha0⟩ := (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).trans (Y.vert 0) (Y.vert 2)
    ((Y.adj 0).symm) (Y.adj 1)
  obtain ⟨b, hbL, hb0⟩ := (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).trans (Y.vert 0) x
    ((Y.adj 0).symm) hx1
  have haG1 : a ∈ Y.Gi 1 := Y.L_le_Gi 1 haL
  have hbG1 : b ∈ Y.Gi 1 := Y.L_le_Gi 1 hbL
  have hbInvG1 : b⁻¹ ∈ Y.Gi 1 := (Y.Gi 1).inv_mem hbG1
  have hbInvx : b⁻¹ • x = Y.vert 0 := by
    calc b⁻¹ • x = b⁻¹ • (b • Y.vert 0) := by rw [hb0]
      _ = Y.vert 0 := inv_smul_smul b (Y.vert 0)
  let F : V → Set ↥(Y.Q 1) := fun v => {y | y ∈ Mset Y x ∧ (y : G) ^ 2 ∈ vertZ (G := G) v}
  have hnoM : ∀ y : ↥(Y.Q 1), y ∈ Mset Y x → (y : G) ^ 2 ≠ 1 := by
    intro y hyM hy2
    exact hno (y : G) y.2 hyM.1 hy2
  have hdisj : ∀ {v w : V}, vertZ (G := G) v ⊓ vertZ (G := G) w = ⊥ →
      Disjoint (F v) (F w) := by
    intro v w hvw
    rw [Set.disjoint_left]
    intro y hyv hyw
    have hmem : (y : G) ^ 2 ∈ vertZ (G := G) v ⊓ vertZ (G := G) w :=
      Subgroup.mem_inf.mpr ⟨hyv.2, hyw.2⟩
    rw [hvw] at hmem
    exact hnoM y hyv.1 (Subgroup.mem_bot.mp hmem)
  have hdisj02 : Disjoint (F (Y.vert 0)) (F (Y.vert 2)) := hdisj hZ02bot
  have hdisj2x : Disjoint (F (Y.vert 2)) (F x) :=
    hdisj (by rw [inf_comm]; exact hZxZ2)
  have hdisj0x : Disjoint (F (Y.vert 0)) (F x) :=
    hdisj (by rw [inf_comm]; exact hZxZ0)
  have hZunion_eq := relSet_Z_one_eq_union Y H hZ h5 hx1 hx0 hx2
  have hcover : Mset Y x ⊆ F (Y.vert 0) ∪ F (Y.vert 2) ∪ F x := by
    intro y hyM
    have hy2Q : (y : G) ^ 2 ∈ Y.Q 1 := (Y.Q 1).pow_mem y.2 2
    have hy2Z1 : (y : G) ^ 2 ∈ Y.Z 1 :=
      (isElemSec_Z_one_Q_one Y H hZ h5).2.2 (y : G) y.2
    have hmemZ1 : (⟨(y : G) ^ 2, hy2Q⟩ : ↥(Y.Q 1)) ∈ relSet (Y.Q 1) (Y.Z 1) := hy2Z1
    rw [← hZunion_eq] at hmemZ1
    rcases hmemZ1 with (h | h) | h
    · exact Or.inl (Or.inl ⟨hyM, h⟩)
    · exact Or.inl (Or.inr ⟨hyM, h⟩)
    · exact Or.inr ⟨hyM, h⟩
  have hMunion : Mset Y x = F (Y.vert 0) ∪ F (Y.vert 2) ∪ F x := by
    refine le_antisymm hcover ?_
    intro y hy
    rcases hy with (hy | hy) | hy
    · exact hy.1
    · exact hy.1
    · exact hy.1
  have hdisj_union_x : Disjoint (F (Y.vert 0) ∪ F (Y.vert 2)) (F x) := by
    rw [Set.disjoint_left]
    intro y hy hyx
    rcases hy with hy0 | hy2
    · exact (Set.disjoint_left.mp hdisj0x) hy0 hyx
    · exact (Set.disjoint_left.mp hdisj2x) hy2 hyx
  have hMsum : (Mset Y x).ncard = (F (Y.vert 0)).ncard + (F (Y.vert 2)).ncard +
      (F x).ncard := by
    rw [hMunion, Set.ncard_union_eq hdisj_union_x, Set.ncard_union_eq hdisj02]
  have hF02 : (F (Y.vert 2)).ncard = (F (Y.vert 0)).ncard :=
    ncard_fibre_smul Y H hx1 hx0 hx2 haG1 ha0
  have hF0x : (F x).ncard = (F (Y.vert 0)).ncard := by
    rw [ncard_fibre_smul Y H hx1 hx0 hx2 hbInvG1 hbInvx]
  have hFsum : (F (Y.vert 0)).ncard + (F (Y.vert 2)).ncard + (F x).ncard =
      3 * (F (Y.vert 0)).ncard := by
    rw [hF02, hF0x]
    ring
  rw [hMsum, hFsum]

private theorem three_dvd_ncard_sq_fibre (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) {x : V} (hx1 : Γ.Adj (Y.vert 1) x) (hx0 : x ≠ Y.vert 0)
    (hx2 : x ≠ Y.vert 2) :
    3 ∣ {y : ↥(Y.Q 1) | y ∈ Mset Y x ∧
      (y : G) ^ 2 ∈ vertZ (G := G) (Y.vert 0)}.ncard := by
  haveI : Finite ↥(Y.Q 1) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  obtain ⟨k, hkK, hk3⟩ := exists_order_three_K Y H hZ h5
  have hkG1 : k ∈ Y.Gi 1 := Y.K_le_Gi 1 hkK
  have hkG : k ∈ Y.Gi 0 ⊓ Y.Gi 1 := ⟨Y.K_le_Gi 0 hkK, hkG1⟩
  have hZ1leQ0 : Y.Z 1 ≤ Y.Q 0 := by
    rw [← (caseC_n Y H hZ h5).2.2.2]
    exact inf_le_left
  have hcent : Y.Q 1 ⊓ Subgroup.centralizer ({k} : Set G) = Y.Z 1 :=
    caseC_cent3 Y H hZ h5 k hkG hk3
  have hk0 : k • Y.vert 0 = Y.vert 0 := Y.K_fix k hkK 0
  have hk2 : k • Y.vert 2 = Y.vert 2 := Y.K_fix k hkK 2
  have hk1 : k • Y.vert 1 = Y.vert 1 := Y.K_fix k hkK 1
  have hnbr := adj_one_iff Y H hx1 hx0 hx2
  have hkx : k • x = x := by
    have hknbr : Γ.Adj (Y.vert 1) (k • x) := by
      have h := (Y.hyp.adj_smul k (Y.vert 1) x).mpr hx1
      rwa [hk1] at h
    rcases (hnbr (k • x)).mp hknbr with h | h | h
    · exact absurd (MulAction.injective k (h.trans hk0.symm)) hx0
    · exact absurd (MulAction.injective k (h.trans hk2.symm)) hx2
    · exact h
  have hkInv0 : k⁻¹ • Y.vert 0 = Y.vert 0 := by
    calc k⁻¹ • Y.vert 0 = k⁻¹ • (k • Y.vert 0) := by rw [hk0]
      _ = Y.vert 0 := inv_smul_smul k (Y.vert 0)
  have hkInv2 : k⁻¹ • Y.vert 2 = Y.vert 2 := by
    calc k⁻¹ • Y.vert 2 = k⁻¹ • (k • Y.vert 2) := by rw [hk2]
      _ = Y.vert 2 := inv_smul_smul k (Y.vert 2)
  have hkInvx : k⁻¹ • x = x := by
    calc k⁻¹ • x = k⁻¹ • (k • x) := by rw [hkx]
      _ = x := inv_smul_smul k x
  have hprek : ({k⁻¹ • Y.vert 0, k⁻¹ • Y.vert 2, k⁻¹ • x} : Set V) =
      {Y.vert 0, Y.vert 2, x} := by
    rw [hkInv0, hkInv2, hkInvx]
  have hkM : ∀ y : ↥(Y.Q 1), y ∈ Mset Y x → conjOnQ Y hkG1 y ∈ Mset Y x := fun y hy =>
    (conjOnQ_mem_Mset_iff Y hkG1 y hprek).mpr hy
  have hZ1cent : Y.Z 1 ≤ Subgroup.centralizer ({k} : Set G) := by
    intro z hz
    have hz' : z ∈ Y.Q 1 ⊓ Subgroup.centralizer ({k} : Set G) := by
      rw [hcent]
      exact hz
    exact (Subgroup.mem_inf.mp hz').2
  have hk_sq : ∀ y : ↥(Y.Q 1), ((conjOnQ Y hkG1 y : G) ^ 2) = (y : G) ^ 2 := by
    intro y
    have hy2Z1 : (y : G) ^ 2 ∈ Y.Z 1 :=
      (isElemSec_Z_one_Q_one Y H hZ h5).2.2 (y : G) y.2
    have hcomm : k * ((y : G) * (y : G)) = ((y : G) * (y : G)) * k := by
      simpa [pow_two] using
        (Subgroup.mem_centralizer_singleton_iff.mp (hZ1cent hy2Z1)).symm
    rw [conjOnQ_apply, pow_two, pow_two]
    calc (k * (y : G) * k⁻¹) * (k * (y : G) * k⁻¹)
        = k * ((y : G) * (y : G)) * k⁻¹ := by group
      _ = (y : G) * (y : G) := by rw [hcomm]; group
  have hkF : ∀ y : ↥(Y.Q 1),
      y ∈ {y : ↥(Y.Q 1) | y ∈ Mset Y x ∧
        (y : G) ^ 2 ∈ vertZ (G := G) (Y.vert 0)} →
      conjOnQ Y hkG1 y ∈ {y : ↥(Y.Q 1) | y ∈ Mset Y x ∧
        (y : G) ^ 2 ∈ vertZ (G := G) (Y.vert 0)} := by
    intro y hy
    exact ⟨hkM y hy.1, by rw [hk_sq y]; exact hy.2⟩
  have hkno : ∀ y : ↥(Y.Q 1),
      y ∈ {y : ↥(Y.Q 1) | y ∈ Mset Y x ∧
        (y : G) ^ 2 ∈ vertZ (G := G) (Y.vert 0)} → conjOnQ Y hkG1 y ≠ y := by
    intro y hy hfix
    have h' : k * (y : G) * k⁻¹ = (y : G) := by
      simpa only [conjOnQ_apply] using congrArg Subtype.val hfix
    have hky : k * (y : G) = (y : G) * k := by
      calc k * (y : G) = (k * (y : G) * k⁻¹) * k := by group
        _ = (y : G) * k := by rw [h']
    have hcenty : (y : G) ∈ Subgroup.centralizer ({k} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hky.symm
    have hyZ : (y : G) ∈ Y.Z 1 := by
      have : (y : G) ∈ Y.Q 1 ⊓ Subgroup.centralizer ({k} : Set G) :=
        Subgroup.mem_inf.mpr ⟨y.2, hcenty⟩
      rwa [hcent] at this
    exact hy.1.1 (hZ1leQ0 hyZ)
  have hk3pow : k * k * k = 1 := by
    rw [← pow_three']
    simpa [hk3] using pow_orderOf_eq_one k
  have hσ3 : ∀ y : ↥(Y.Q 1),
      conjOnQ Y hkG1 (conjOnQ Y hkG1 (conjOnQ Y hkG1 y)) = y := by
    intro y
    apply Subtype.ext
    simp only [conjOnQ_apply]
    calc k * (k * (k * (y : G) * k⁻¹) * k⁻¹) * k⁻¹ =
          (k * k * k) * (y : G) * (k * k * k)⁻¹ := by group
      _ = (y : G) := by rw [hk3pow]; group
  classical
  let S : Set ↥(Y.Q 1) :=
    {y : ↥(Y.Q 1) | y ∈ Mset Y x ∧ (y : G) ^ 2 ∈ vertZ (G := G) (Y.vert 0)}
  have hSfin : S.Finite := Set.toFinite S
  have hdvd : 3 ∣ S.ncard := by
    rw [Set.ncard_eq_toFinset_card S hSfin]
    exact CFSG.Quasithin.HSType.prime_dvd_card_of_free hSfin.toFinset (conjOnQ Y hkG1)
      Nat.prime_three (fun a _ => hσ3 a)
      (fun a ha => hSfin.mem_toFinset.mpr (hkF a (hSfin.mem_toFinset.mp ha)))
      (fun a ha => hkno a (hSfin.mem_toFinset.mp ha))
  simpa [S] using hdvd

private theorem caseC_inv (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) : ∃ x ∈ Y.Q 1, x ∉ Y.Q 0 ∧ x ^ 2 = 1 := by
  obtain ⟨x, hx1, hx0, hx2⟩ := Y.exists_third_nbr
  by_contra hcon
  push Not at hcon
  have hMcard : (Mset Y x).ncard = 24 := ncard_Mset Y H hZ h5 hx1 hx0 hx2
  have hthree := ncard_Mset_eq_three_mul Y H hZ h5 hx1 hx0 hx2 hcon
  have hdvd := three_dvd_ncard_sq_fibre Y H hZ h5 hx1 hx0 hx2
  have hS8 : {y : ↥(Y.Q 1) | y ∈ Mset Y x ∧
      (y : G) ^ 2 ∈ vertZ (G := G) (Y.vert 0)}.ncard = 8 := by
    omega
  rw [hS8] at hdvd
  norm_num at hdvd

private theorem isQ8D8_of_eq {P P' : Subgroup G} (h : P = P') (hq : IsQ8D8 ↥P) :
    IsQ8D8 ↥P' :=
  h ▸ hq

theorem treeJ2_of_caseC (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h5 : s = 5) : Y.swap.TreeJ2Data := by
  have hcardQ1 : Nat.card ↥(Y.Q 1) = 2 ^ 6 := card_Q_one_of_caseC Y H hZ h5
  have hZ1 : Y.Q 0 ⊓ Y.Q 2 = Y.Z 1 := (caseC_n Y H hZ h5).2.2.2
  have hZ1Q0 : Y.Z 1 ≤ Y.Q 0 := by
    rw [← hZ1]
    exact inf_le_left
  have hZ1card : Nat.card ↥(Y.Z 1) = 4 := (s52_step8_Z Y H hZ 1 (by norm_num)).2
  have hZ1elem : IsElemAbelian 2 (Y.Z 1) := (s52_step8_Z Y H hZ 1 (by norm_num)).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Setup.swap_S] using (caseC_n Y H hZ h5).2.1
  · exact isQ8D8_of_eq (by simpa using Setup.swap_Q (X := Y) 1)
      (caseC_q8d8 Y H hZ h5)
  · simpa [Setup.swap_Q] using hcardQ1
  · simpa [Setup.swap_Z] using hZ1card
  · simpa [Setup.swap_Z] using hZ1elem
  · simpa [Setup.swap_L, Setup.swap_Q] using caseC_nat Y H hZ h5
  · simpa [Setup.swap_Z, Setup.swap_Q] using hZ1Q0
  · intro k hk hk3
    have hk' : (k • Y.vert 1 = Y.vert 1) ∧ (k • Y.vert 0 = Y.vert 0) := by
      simpa [Setup.swap_Gi] using hk
    have hmem : k ∈ Y.Gi 0 ⊓ Y.Gi 1 := ⟨hk'.2, hk'.1⟩
    simpa [Setup.swap_Gi, Setup.swap_Q, Setup.swap_Z] using
      caseC_cent3 Y H hZ h5 k hmem hk3
  · simpa [Setup.swap_Q] using caseC_inv Y H hZ h5

end Setup

end CFSG.Quasithin.St84
