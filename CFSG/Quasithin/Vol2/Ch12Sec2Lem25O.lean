module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3Cs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL4L5
public import CFSG.Quasithin.Background.FLcLn
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

namespace Lem25

theorem two_lt_card_pCore_perfectCore {n : ℕ} (hn5 : n ≤ 5) {I : Set ℕ} {a m : ℕ}
    (h : a + m ≤ n) (hm3 : 3 ≤ m) (hmn : m < n) (ha : a = 0 ∨ a ∈ I)
    (hb : a + m = n ∨ a + m ∈ I) (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) :
    2 < Nat.card (CFSG.pCore 2 ↥(perfectCore (flagStabilizer n (ZMod 2) I))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  set H := flagStabilizer n (ZMod 2) I with hH
  set P := perfectCore H with hP
  set P₀ : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2)) :=
    Subgroup.closure {x | ∃ (i j : Fin m) (hij : i ≠ j), x = liftT a m h hij} with hP₀
  have hP₀H : P₀ ≤ H := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, j, hij, rfl⟩
    exact liftT_mem_flagStabilizer a m h hno hij
  have hgen : ∀ (i j : Fin m) (hij : i ≠ j), liftT a m h hij ∈ P₀ := fun i j hij =>
    Subgroup.subset_closure ⟨i, j, hij, rfl⟩
  have hP₀perf : ⁅P₀, P₀⁆ = P₀ := by
    have h1 : ⁅P₀, P₀⁆ ≤ P₀ := Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
    have h2 : P₀ ≤ ⁅P₀, P₀⁆ := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, j, hij, rfl⟩
      obtain ⟨k, hki, hkj⟩ : ∃ k : Fin m, k ≠ i ∧ k ≠ j := by
        by_contra hcon
        push Not at hcon
        have hsub : (Finset.univ : Finset (Fin m)) ⊆ {i, j} := fun k _ => by
          by_cases hki : k = i
          · simp [hki]
          · simp [hcon k hki]
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_le_two (a := i) (b := j)
        simp only [Finset.card_univ, Fintype.card_fin] at h1
        omega
      have hcomm : ⁅(liftT a m h (Ne.symm hki) : SpecialLinearGroup (Fin n) (ZMod 2)),
          (liftT a m h hkj : SpecialLinearGroup (Fin n) (ZMod 2))⁆ = liftT a m h hij := by
        have := SpecialLinearGroup.commutatorElement_transvection
          (blkIdxN_ne (h := h) (Ne.symm hki)) (blkIdxN_ne (h := h) hkj)
          (blkIdxN_ne (h := h) hij) (1 : ZMod 2) 1
        rw [mul_one] at this
        exact this
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator (hgen _ _ _) (hgen _ _ _)
    exact le_antisymm h1 h2
  have hlift : ∀ (i j : Fin m) (hij : i ≠ j),
      (liftT a m h hij : SpecialLinearGroup (Fin n) (ZMod 2)) ∈ P := fun i j hij =>
    le_perfectCore_of_perfect hP₀H hP₀perf (hgen i j hij)
  have hPn : ∀ g ∈ H, ∀ x ∈ P, g * x * g⁻¹ ∈ P := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_perfectCore H
      (Subgroup.le_normalizer hg)) x).mp hx
  have hup : ∀ (i j : Fin n) (hij : i ≠ j), (i : ℕ) < j →
      (SpecialLinearGroup.transvection hij (1 : ZMod 2) : SpecialLinearGroup (Fin n) (ZMod 2)) ∈
        H := by
    intro i j hij hlt
    refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
    rw [CFSG.LinearGroups.coe_transvection]
    have hkl : k ≠ l := fun e => by subst e; omega
    have hne : ¬ (i = k ∧ j = l) := by
      rintro ⟨rfl, rfl⟩
      omega
    simp [hkl, hne]
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  set i₁ : Fin m := ⟨0, hm0⟩ with hi₁
  set i₂ : Fin m := ⟨1, hm1⟩ with hi₂
  have h12 : i₁ ≠ i₂ := by simp [hi₁, hi₂, Fin.ext_iff]
  have hb12 : blkIdxN a m h i₁ ≠ blkIdxN a m h i₂ := blkIdxN_ne h12
  obtain ⟨x₁, x₂, hx₁, hx₂, hx₁1, hx₂1, hx12, hb₁, hb₂⟩ :
      ∃ x₁ x₂ : SpecialLinearGroup (Fin n) (ZMod 2), x₁ ∈ P ∧ x₂ ∈ P ∧ x₁ ≠ 1 ∧ x₂ ≠ 1 ∧
        x₁ ≠ x₂ ∧ blkAt a m h (x₁ : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 ∧
        blkAt a m h (x₂ : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    by_cases hlt : a + m < n
    ·
      set j : Fin n := ⟨a + m, hlt⟩ with hj
      have hij : ∀ r : Fin m, blkIdxN a m h r ≠ j := fun r e => by
        have h1 := congrArg Fin.val e
        simp only [blkIdxN, hj] at h1
        have := r.isLt
        omega
      have hlt' : ∀ r : Fin m, ((blkIdxN a m h r : Fin n) : ℕ) < j := fun r => by
        simp only [blkIdxN, hj]
        have := r.isLt
        omega
      have hmem : ∀ (r s : Fin m) (hrs : r ≠ s),
          (SpecialLinearGroup.transvection (hij r) (1 : ZMod 2) :
            SpecialLinearGroup (Fin n) (ZMod 2)) ∈ P := by
        intro r s hrs
        have hcomm := SpecialLinearGroup.commutatorElement_transvection
          (blkIdxN_ne (h := h) hrs) (hij s) (hij r) (1 : ZMod 2) 1
        rw [mul_one] at hcomm
        rw [← hcomm, commutatorElement_def]
        have hA : (SpecialLinearGroup.transvection (blkIdxN_ne (h := h) hrs) (1 : ZMod 2) :
            SpecialLinearGroup (Fin n) (ZMod 2)) ∈ P := hlift r s hrs
        have hB := hup _ _ (hij s) (hlt' s)
        have h1 := hPn _ hB _ (P.inv_mem hA)
        have h2 := P.mul_mem hA h1
        simpa [mul_assoc] using h2
      have hent : ∀ r : Fin m, ∀ (x y : Fin n), ((SpecialLinearGroup.transvection (hij r)
          (1 : ZMod 2) : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
            x y = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) x y +
              if x = blkIdxN a m h r ∧ y = j then 1 else 0 := by
        intro r x y
        rw [CFSG.LinearGroups.coe_transvection, Matrix.add_apply, Matrix.single_apply]
        congr 1
        exact if_congr ⟨fun h' => ⟨h'.1.symm, h'.2.symm⟩, fun h' => ⟨h'.1.symm, h'.2.symm⟩⟩
          rfl rfl
      refine ⟨_, _, hmem i₁ i₂ h12, hmem i₂ i₁ h12.symm, ?_, ?_, ?_, ?_, ?_⟩
      · intro e
        have h1 := congrArg (fun A : SpecialLinearGroup (Fin n) (ZMod 2) =>
          (A : Matrix (Fin n) (Fin n) (ZMod 2)) (blkIdxN a m h i₁) j) e
        rw [hent] at h1
        simp [hij i₁] at h1
      · intro e
        have h1 := congrArg (fun A : SpecialLinearGroup (Fin n) (ZMod 2) =>
          (A : Matrix (Fin n) (Fin n) (ZMod 2)) (blkIdxN a m h i₂) j) e
        rw [hent] at h1
        simp [hij i₂] at h1
      · intro e
        have h1 := congrArg (fun A : SpecialLinearGroup (Fin n) (ZMod 2) =>
          (A : Matrix (Fin n) (Fin n) (ZMod 2)) (blkIdxN a m h i₁) j) e
        rw [hent, hent] at h1
        simp [hij i₁, hb12] at h1
      · ext s t
        rw [blkAt_apply, hent]
        have : ¬ ((⟨a + t, by have := t.isLt; omega⟩ : Fin n) = j) := fun e => by
          have h1 := congrArg Fin.val e
          simp only [hj] at h1
          have := t.isLt
          omega
        simp [Matrix.one_apply, Fin.ext_iff, this]
      · ext s t
        rw [blkAt_apply, hent]
        have : ¬ ((⟨a + t, by have := t.isLt; omega⟩ : Fin n) = j) := fun e => by
          have h1 := congrArg Fin.val e
          simp only [hj] at h1
          have := t.isLt
          omega
        simp [Matrix.one_apply, Fin.ext_iff, this]
    ·
      have ha1 : 1 ≤ a := by omega
      set j : Fin n := ⟨a - 1, by omega⟩ with hj
      have hij : ∀ r : Fin m, j ≠ blkIdxN a m h r := fun r e => by
        have h1 := congrArg Fin.val e
        simp only [blkIdxN, hj] at h1
        omega
      have hlt' : ∀ r : Fin m, (j : ℕ) < blkIdxN a m h r := fun r => by
        simp only [blkIdxN, hj]
        omega
      have hmem : ∀ (r s : Fin m) (hrs : r ≠ s),
          (SpecialLinearGroup.transvection (hij r) (1 : ZMod 2) :
            SpecialLinearGroup (Fin n) (ZMod 2)) ∈ P := by
        intro r s hrs
        have hcomm := SpecialLinearGroup.commutatorElement_transvection
          (hij s) (blkIdxN_ne (h := h) (Ne.symm hrs)) (hij r) (1 : ZMod 2) 1
        rw [mul_one] at hcomm
        rw [← hcomm, commutatorElement_def]
        have hA : (SpecialLinearGroup.transvection (blkIdxN_ne (h := h) (Ne.symm hrs))
            (1 : ZMod 2) : SpecialLinearGroup (Fin n) (ZMod 2)) ∈ P := hlift s r (Ne.symm hrs)
        have hB := hup _ _ (hij s) (hlt' s)
        have h1 := hPn _ hB _ hA
        exact P.mul_mem h1 (P.inv_mem hA)
      have hent : ∀ r : Fin m, ∀ (x y : Fin n), ((SpecialLinearGroup.transvection (hij r)
          (1 : ZMod 2) : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
            x y = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) x y +
              if x = j ∧ y = blkIdxN a m h r then 1 else 0 := by
        intro r x y
        rw [CFSG.LinearGroups.coe_transvection, Matrix.add_apply, Matrix.single_apply]
        congr 1
        exact if_congr ⟨fun h' => ⟨h'.1.symm, h'.2.symm⟩, fun h' => ⟨h'.1.symm, h'.2.symm⟩⟩
          rfl rfl
      refine ⟨_, _, hmem i₁ i₂ h12, hmem i₂ i₁ h12.symm, ?_, ?_, ?_, ?_, ?_⟩
      · intro e
        have h1 := congrArg (fun A : SpecialLinearGroup (Fin n) (ZMod 2) =>
          (A : Matrix (Fin n) (Fin n) (ZMod 2)) j (blkIdxN a m h i₁)) e
        rw [hent] at h1
        simp [hij i₁] at h1
      · intro e
        have h1 := congrArg (fun A : SpecialLinearGroup (Fin n) (ZMod 2) =>
          (A : Matrix (Fin n) (Fin n) (ZMod 2)) j (blkIdxN a m h i₂)) e
        rw [hent] at h1
        simp [hij i₂] at h1
      · intro e
        have h1 := congrArg (fun A : SpecialLinearGroup (Fin n) (ZMod 2) =>
          (A : Matrix (Fin n) (Fin n) (ZMod 2)) j (blkIdxN a m h i₁)) e
        rw [hent, hent] at h1
        simp [hij i₁, hb12] at h1
      · ext s t
        rw [blkAt_apply, hent]
        have : ¬ ((⟨a + s, by have := s.isLt; omega⟩ : Fin n) = j) := fun e => by
          have h1 := congrArg Fin.val e
          simp only [hj] at h1
          omega
        simp [Matrix.one_apply, Fin.ext_iff, this]
      · ext s t
        rw [blkAt_apply, hent]
        have : ¬ ((⟨a + s, by have := s.isLt; omega⟩ : Fin n) = j) := fun e => by
          have h1 := congrArg Fin.val e
          simp only [hj] at h1
          omega
        simp [Matrix.one_apply, Fin.ext_iff, this]
  set β := bigBlockHom (K := ZMod 2) I a m h ha hb with hβ
  have hker2 : IsPGroup 2 β.ker := by
    intro x
    have hxU := unitriangular_of_bigBlockHom hK hn5 h hm3 ha hb hno (x : ↥P) x.2
    obtain ⟨k, hk⟩ := isPGroup_unitriangular_charTwo (K := ZMod 2) (n := n) (by omega) ⟨_, hxU⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hkerO : β.ker ≤ CFSG.pCore 2 ↥P := le_sSup ⟨β.normal_ker, hker2⟩
  have hβx : ∀ (x : SpecialLinearGroup (Fin n) (ZMod 2)) (hx : x ∈ P),
      blkAt a m h (x : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 → (⟨x, hx⟩ : ↥P) ∈ β.ker :=
    fun x hx hbx => MonoidHom.mem_ker.mpr (Subtype.ext (by rw [bigBlockHom_coe]; exact hbx))
  let f : Fin 3 → ↥(CFSG.pCore 2 ↥P) :=
    ![1, ⟨⟨x₁, hx₁⟩, hkerO (hβx x₁ hx₁ hb₁)⟩, ⟨⟨x₂, hx₂⟩, hkerO (hβx x₂ hx₂ hb₂)⟩]
  have hg : ∀ u : Fin 3, ((f u : ↥P) : SpecialLinearGroup (Fin n) (ZMod 2)) =
      ![(1 : SpecialLinearGroup (Fin n) (ZMod 2)), x₁, x₂] u := by
    intro u
    fin_cases u <;> rfl
  have hf : Function.Injective f := by
    intro u v huv
    have h1 : ![(1 : SpecialLinearGroup (Fin n) (ZMod 2)), x₁, x₂] u =
        ![(1 : SpecialLinearGroup (Fin n) (ZMod 2)), x₁, x₂] v := by
      rw [← hg, ← hg, huv]
    fin_cases u <;> fin_cases v <;>
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Fin.reduceFinMk] at h1 <;>
      first
      | rfl
      | exact absurd h1.symm hx₁1
      | exact absurd h1 hx₁1
      | exact absurd h1.symm hx₂1
      | exact absurd h1 hx₂1
      | exact absurd h1 hx12
      | exact absurd h1.symm hx12
  have h3 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin] at h3
  omega


theorem perfectCore_subgroupOf' {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hHK : H ≤ K) : perfectCore (H.subgroupOf K) = (perfectCore H).subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [map_perfectCore, Subgroup.subgroupOf_map_subtype, inf_of_le_left hHK,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left ((perfectCore_le H).trans hHK)]

theorem card_pCore_congr {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y) :
    Nat.card (CFSG.pCore 2 X) = Nat.card (CFSG.pCore 2 Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (CFSG.pCore 2 X).map e.toMonoidHom = CFSG.pCore 2 Y := by
    apply le_antisymm
    · exact le_sSup ⟨Subgroup.Normal.map CFSG.pCore_normal _ e.surjective,
        (CFSG.pCore_isPGroup (p := 2) (G := X)).map _⟩
    · intro y hy
      refine ⟨e.symm y, ?_, by simp⟩
      have hle : (CFSG.pCore 2 Y).map e.symm.toMonoidHom ≤ CFSG.pCore 2 X :=
        le_sSup ⟨Subgroup.Normal.map CFSG.pCore_normal _ e.symm.surjective,
          (CFSG.pCore_isPGroup (p := 2) (G := Y)).map _⟩
      exact hle ⟨y, hy, rfl⟩
  rw [← h1, Subgroup.card_map_of_injective e.injective]

theorem not_c4_c5 {Q : Type} [Group Q] [Finite Q] {B K : Subgroup Q} {k c : ℕ}
    (hD : Data1293 B k c) (hO2 : Nat.card (CFSG.pCore 2 ↥B) ≤ 2)
    (h : A312C4 B K ∨ A312C5 B K) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, hKm, hcm, P, hP, rfl⟩ : ∃ m, (m = 4 ∨ m = 5) ∧ IsPSL m 2 1 ↥K ∧
      (c = 168 ∨ (m = 5 ∧ c = 20160)) ∧ ∃ P, IsParabolic2 K P ∧ B = perfectCore P := by
    rcases h with ⟨hB, hK | hK, hP⟩ | ⟨hB, hK, hP⟩
    · exact ⟨4, Or.inl rfl, hK, Or.inl (hD.cardQ.symm.trans
        (Vol2.Ch11.SecB.card_isPSL_three_two_one hB)), hP⟩
    · exact ⟨5, Or.inr rfl, hK, Or.inl (hD.cardQ.symm.trans
        (Vol2.Ch11.SecB.card_isPSL_three_two_one hB)), hP⟩
    · exact ⟨5, Or.inr rfl, hK, Or.inr ⟨rfl, hD.cardQ.symm.trans
        (Vol2.Ch11.SecB.card_isPSL_four_two_one hB)⟩, hP⟩
  obtain ⟨e₀⟩ := nonempty_mulEquiv_sl_of_isPSL hKm
  obtain ⟨hPK, S, hS, hSP⟩ := hP
  obtain ⟨D⟩ := FLc.exists_borelIso (by omega) hS e₀
  have hSK : S ≤ K := hS.1
  have hSP' : S ≤ P := fun s hs => hSP ⟨hSK hs, Subgroup.le_normalizer hs⟩
  have hUP : FLc.Ut m ≤ D.model P := (D.Ut_le_model_iff hSK).mpr hSP'
  have hQI := FLc.eq_QI_cuts hUP
  set I := FLc.cuts (D.model P) with hI
  have hmodel : D.model (perfectCore P) = perfectCore (FLc.QI m I) := by
    show ((perfectCore P).subgroupOf K).map D.e.toMonoidHom = _
    rw [← perfectCore_subgroupOf' hPK, map_perfectCore]
    exact congrArg perfectCore hQI
  have hBK : perfectCore P ≤ K := (perfectCore_le P).trans hPK
  let eB : ↥(perfectCore P) ≃* ↥(perfectCore (FLc.QI m I)) :=
    ((Subgroup.subgroupOfEquivOfLe hBK).symm.trans
      (D.e.subgroupMap ((perfectCore P).subgroupOf K))).trans
      (MulEquiv.subgroupCongr hmodel)
  have hcard : Nat.card (CFSG.pCore 2 ↥(perfectCore P)) =
      Nat.card (CFSG.pCore 2 ↥(perfectCore (FLc.QI m I))) := card_pCore_congr eB
  have hcardB : Nat.card ↥(perfectCore P) = Nat.card ↥(perfectCore (FLc.QI m I)) :=
    Nat.card_congr eB.toEquiv
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hc : c = 168 ∨ c = 20160 := hD.c_eq
  obtain ⟨a₀, ha₀⟩ := hD.card
  rcases exists_big_or_small (n := m) (I := I) with hsmall | ⟨a, m', h, hm3, ha, hb, hno⟩
  ·
    have hbot := perfectCore_eq_bot_of_small hK2 (by omega) hsmall
    rw [hbot, Subgroup.card_bot] at hcardB
    rw [hcardB] at ha₀
    rcases hc with rfl | rfl
    · have : 1 ≤ 2 ^ a₀ := Nat.one_le_two_pow
      omega
    · have : 1 ≤ 2 ^ a₀ := Nat.one_le_two_pow
      omega
  · by_cases hmm : m' < m
    · have h1 : 2 < Nat.card (CFSG.pCore 2 ↥(perfectCore (FLc.QI m I))) :=
        two_lt_card_pCore_perfectCore (by omega) h hm3 hmm ha hb hno
      omega
    ·
      have hm' : m' = m := by omega
      have ha0 : a = 0 := by omega
      subst ha0 hm'
      have hIe : I = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro i hi
        have hn := FLc.isNode_of_mem_cuts (hI ▸ hi : i ∈ FLc.cuts (D.model P))
        exact hno i hi ⟨by have := hn.1; omega, by have := hn.2; omega⟩
      have htop : FLc.QI m' ∅ = ⊤ := flagStabilizer_empty m' (ZMod 2)
      have hperf : perfectCore (⊤ : Subgroup (SpecialLinearGroup (Fin m') (ZMod 2))) = ⊤ := by
        rw [perfectCore_eq_self_iff]
        exact (isQuasisimple_sl_zmod_two (m := m') (by omega)).1.1.commutator_eq_top
      rw [hIe, htop, hperf, Subgroup.card_top, ← Nat.card_congr e₀.toEquiv] at hcardB
      have card5 : IsPSL 5 2 1 ↥K → Nat.card ↥K = 9999360 := fun hK => by
        rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hK).1 rfl]
        decide
      have hpow : ∀ x : ℕ, x < 2 ^ 16 → 2 ^ a₀ = x → a₀ < 16 := fun x hx hax => by
        by_contra hge
        have : 2 ^ 16 ≤ 2 ^ a₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rcases hcm with rfl | ⟨rfl, rfl⟩
      · rcases hm with rfl | rfl
        · rw [Vol2.Ch11.SecB.card_isPSL_four_two_one hKm] at hcardB
          have h1 : 2 ^ a₀ = 120 := by omega
          have h16 := hpow 120 (by norm_num) h1
          interval_cases a₀ <;> norm_num at h1
        · rw [card5 hKm] at hcardB
          have h1 : 2 ^ a₀ = 59520 := by omega
          have h16 := hpow 59520 (by norm_num) h1
          interval_cases a₀ <;> norm_num at h1
      · rw [card5 hKm] at hcardB
        have h1 : 2 ^ a₀ = 496 := by omega
        have h16 := hpow 496 (by norm_num) h1
        interval_cases a₀ <;> norm_num at h1

end Lem25

end CFSG.Quasithin.H13
