module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_zpowers_le_of_inf_centralizer_ne_bot {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {I P Z B : Subgroup G} {t : G} (hI : IsElemAbelian 2 I) (hP : IsElemAbelian p P)
    (hPI : P ≤ Subgroup.normalizer (I : Set G))
    (htI : t ∈ Subgroup.normalizer (I : Set G)) (htP : t ∈ Subgroup.normalizer (P : Set G))
    (hZP : Z ≤ P) (hZt : Z ≤ Subgroup.centralizer ({t} : Set G))
    (hZcard : Nat.card Z * p = Nat.card P)
    (hIt : ⁅I, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (Z : Set G))
    (hB : B ≤ P) (hBcard : Nat.card B * p = Nat.card P) (hBZ : B ≠ Z)
    (hne : ⁅I, P⁆ ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥) :
    ⁅P, Subgroup.zpowers t⁆ ≤ B := by
  classical
  set A : Subgroup G := ⁅I, P⁆ with hA_def
  have hA_le_I : A ≤ I := by
    rw [hA_def]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hPI
  have hAab : IsMulCommutative ↥A :=
    IsMulCommutative.of_comm fun x y => by
      apply Subtype.ext
      simpa using congrArg Subtype.val
        (hI.1.is_comm.comm (⟨x, hA_le_I x.2⟩ : ↥I) ⟨y, hA_le_I y.2⟩)
  have hAe : IsElemAbelian 2 A := ⟨hAab, fun x hx => hI.2 x (hA_le_I hx)⟩
  have hPp : IsPGroup p P := fun y => ⟨1, Subtype.ext (by simpa using hP.2 y y.2)⟩
  have hPA : P ≤ Subgroup.normalizer (A : Set G) := by
    rw [hA_def]
    exact Subgroup.normalizer_commutator_ge_right I P
  have hAP : A ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
    rw [hA_def]
    exact commutator_inf_centralizer_right_eq_bot hp2 hI hPp hPI
  have hneA : A ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
    simpa only [hA_def] using hne
  have htA : t ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hA_def, Subgroup.map_commutator]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp htI,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htP]
  have hAt_le_CZ : ⁅A, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (Z : Set G) :=
    (Subgroup.commutator_mono hA_le_I le_rfl).trans hIt
  set B' : Subgroup G := conjSubgroup B t⁻¹ with hB'_def
  have hB'P : B' ≤ P := by
    intro x hx
    rw [hB'_def, mem_conjSubgroup_iff] at hx
    have hx' : t⁻¹ * x * t ∈ B := by simpa only [inv_inv] using hx
    exact (Subgroup.mem_normalizer_iff''.mp htP x).mpr (hB hx')
  have hB'card : Nat.card B' * p = Nat.card P := by
    have hc : Nat.card B' = Nat.card B := by
      rw [hB'_def, conjSubgroup]
      exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj ((t⁻¹)⁻¹)))
    rw [hc, hBcard]
  have htB : conjSubgroup B t⁻¹ = B := by
    by_cases h1 : conjSubgroup B t⁻¹ = B
    · exact h1
    · by_cases h2 : conjSubgroup B t⁻¹ = Z
      · exfalso
        have hBleZ : B ≤ Z := by
          intro b hb
          have htbZ : t * b * t⁻¹ ∈ Z := by
            rw [← h2]
            exact mem_conjSubgroup_iff.mpr (by
              have htb : t⁻¹ * (t * b * t⁻¹) * (t⁻¹)⁻¹ = b := by group
              rwa [htb])
          have hzt : t * (t * b * t⁻¹) = (t * b * t⁻¹) * t :=
            Subgroup.mem_centralizer_iff.mp (hZt htbZ) t (Set.mem_singleton t)
          have hz_fix : t⁻¹ * (t * b * t⁻¹) * t = t * b * t⁻¹ := by
            rw [mul_assoc, hzt.symm, ← mul_assoc, inv_mul_cancel, one_mul]
          have hbeq : b = t * b * t⁻¹ :=
            (by group : b = t⁻¹ * (t * b * t⁻¹) * t).trans hz_fix
          rw [hbeq]
          exact htbZ
        have hBZcard : Nat.card B = Nat.card Z :=
          Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos (hBcard.trans hZcard.symm)
        exact hBZ (Subgroup.eq_of_le_of_card_ge hBleZ (le_of_eq hBZcard.symm))
      · exfalso
        have hsup1 : conjSubgroup B t⁻¹ ⊔ B = P :=
          sup_eq_of_card_mul_eq_of_ne hB'P hB hB'card hBcard h1
        have hsup2 : conjSubgroup B t⁻¹ ⊔ Z = P :=
          sup_eq_of_card_mul_eq_of_ne hB'P hZP hB'card hZcard h2
        have hle1 : A ⊓ Subgroup.centralizer (B : Set G) ≤ ⁅A, conjSubgroup B t⁻¹⁆ :=
          inf_centralizer_le_commutator_of_sup_eq hp2 hAe hPp hP.1 hPA hAP hB'P hB hsup1
        have hle2 : A ⊓ Subgroup.centralizer (Z : Set G) ≤ ⁅A, conjSubgroup B t⁻¹⁆ :=
          inf_centralizer_le_commutator_of_sup_eq hp2 hAe hPp hP.1 hPA hAP hB'P hZP hsup2
        have hB'p : IsPGroup p (conjSubgroup B t⁻¹) := hPp.to_le hB'P
        have hdisj := (CFSG.GroupTheory.card_centralizer_mul_card_commutator_of_coprime
          (W := A) (X := conjSubgroup B t⁻¹) (p := p) hAab hAe.2 hB'p hp2
          (hB'P.trans hPA)).2
        apply hneA
        rw [eq_bot_iff]
        intro a ha
        rw [Subgroup.mem_bot]
        have haA : a ∈ A := ha.1
        have haC : a ∈ Subgroup.centralizer (B : Set G) := ha.2
        have htaA : t * a * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp htA a).mp haA
        have hcA : a⁻¹ * (t * a * t⁻¹) ∈ A := A.mul_mem (A.inv_mem haA) htaA
        have hcCZ : a⁻¹ * (t * a * t⁻¹) ∈ Subgroup.centralizer (Z : Set G) := by
          have hmem : ⁅a⁻¹, t⁆ ∈ ⁅A, Subgroup.zpowers t⁆ :=
            Subgroup.commutator_mem_commutator (A.inv_mem haA) (Subgroup.mem_zpowers t)
          have hCZ := hAt_le_CZ hmem
          convert hCZ using 1
          rw [commutatorElement_def]
          group
        have hcAZ : a⁻¹ * (t * a * t⁻¹) ∈ A ⊓ Subgroup.centralizer (Z : Set G) :=
          Subgroup.mem_inf.mpr ⟨hcA, hcCZ⟩
        have hta_eq : t * a * t⁻¹ = a * (a⁻¹ * (t * a * t⁻¹)) := by group
        have hta_mem1 : a ∈ ⁅A, conjSubgroup B t⁻¹⁆ := hle1 ha
        have hc_mem1 : a⁻¹ * (t * a * t⁻¹) ∈ ⁅A, conjSubgroup B t⁻¹⁆ := hle2 hcAZ
        have hta_comm1 : t * a * t⁻¹ ∈ ⁅A, conjSubgroup B t⁻¹⁆ := by
          rw [hta_eq]
          exact (⁅A, conjSubgroup B t⁻¹⁆).mul_mem hta_mem1 hc_mem1
        have htaC' : t * a * t⁻¹ ∈
            Subgroup.centralizer ((conjSubgroup B t⁻¹ : Subgroup G) : Set G) := by
          rw [Subgroup.mem_centralizer_iff] at haC ⊢
          intro b' hb'
          have hb : t⁻¹ * b' * t ∈ B := by
            simpa only [inv_inv] using mem_conjSubgroup_iff.mp hb'
          have hcomm := haC (t⁻¹ * b' * t) hb
          calc b' * (t * a * t⁻¹)
              = t * ((t⁻¹ * b' * t) * a) * t⁻¹ := by group
            _ = t * (a * (t⁻¹ * b' * t)) * t⁻¹ := by rw [hcomm]
            _ = (t * a * t⁻¹) * b' := by group
        have hta_disj : t * a * t⁻¹ ∈ (⊥ : Subgroup G) := by
          rw [← hdisj]
          exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨htaA, htaC'⟩, hta_comm1⟩
        have hta1 : t * a * t⁻¹ = 1 := Subgroup.mem_bot.mp hta_disj
        have ha1 : a = t⁻¹ * (t * a * t⁻¹) * t := by group
        rw [ha1, hta1]
        group
  have htaB : ∀ a ∈ A ⊓ Subgroup.centralizer (B : Set G), t * a * t⁻¹ = a := by
    intro a ha
    have haA : a ∈ A := ha.1
    have haC : a ∈ Subgroup.centralizer (B : Set G) := ha.2
    have htaA : t * a * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp htA a).mp haA
    have htaCB : t * a * t⁻¹ ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at haC ⊢
      intro b hb
      have hb' : t⁻¹ * b * t ∈ B := by
        rw [← htB] at hb
        simpa only [inv_inv] using mem_conjSubgroup_iff.mp hb
      have hcomm := haC (t⁻¹ * b * t) hb'
      calc b * (t * a * t⁻¹)
          = t * ((t⁻¹ * b * t) * a) * t⁻¹ := by group
        _ = t * (a * (t⁻¹ * b * t)) * t⁻¹ := by rw [hcomm]
        _ = (t * a * t⁻¹) * b := by group
    have hcA : a⁻¹ * (t * a * t⁻¹) ∈ A := A.mul_mem (A.inv_mem haA) htaA
    have hcB : a⁻¹ * (t * a * t⁻¹) ∈ Subgroup.centralizer (B : Set G) :=
      (Subgroup.centralizer (B : Set G)).mul_mem
        ((Subgroup.centralizer (B : Set G)).inv_mem haC) htaCB
    have hcCZ : a⁻¹ * (t * a * t⁻¹) ∈ Subgroup.centralizer (Z : Set G) := by
      have hmem : ⁅a⁻¹, t⁆ ∈ ⁅A, Subgroup.zpowers t⁆ :=
        Subgroup.commutator_mem_commutator (A.inv_mem haA) (Subgroup.mem_zpowers t)
      have hCZ := hAt_le_CZ hmem
      convert hCZ using 1
      rw [commutatorElement_def]
      group
    have hcAZ : a⁻¹ * (t * a * t⁻¹) ∈ A ⊓ Subgroup.centralizer (Z : Set G) :=
      Subgroup.mem_inf.mpr ⟨hcA, hcCZ⟩
    have hcAB : a⁻¹ * (t * a * t⁻¹) ∈ A ⊓ Subgroup.centralizer (B : Set G) :=
      Subgroup.mem_inf.mpr ⟨hcA, hcB⟩
    have hsup3 : B ⊔ Z = P :=
      sup_eq_of_card_mul_eq_of_ne hB hZP hBcard hZcard hBZ
    have hle3 : A ⊓ Subgroup.centralizer (Z : Set G) ≤ ⁅A, B⁆ :=
      inf_centralizer_le_commutator_of_sup_eq hp2 hAe hPp hP.1 hPA hAP hB hZP hsup3
    have hc_mem3 : a⁻¹ * (t * a * t⁻¹) ∈ ⁅A, B⁆ := hle3 hcAZ
    have hBp : IsPGroup p B := hPp.to_le hB
    have hdisj3 := (CFSG.GroupTheory.card_centralizer_mul_card_commutator_of_coprime
      (W := A) (X := B) (p := p) hAab hAe.2 hBp hp2 (hB.trans hPA)).2
    have hc_bot : a⁻¹ * (t * a * t⁻¹) ∈ (⊥ : Subgroup G) := by
      rw [← hdisj3]
      exact Subgroup.mem_inf.mpr ⟨hcAB, hc_mem3⟩
    have hc1 : a⁻¹ * (t * a * t⁻¹) = 1 := Subgroup.mem_bot.mp hc_bot
    have : t * a * t⁻¹ = a := by
      calc t * a * t⁻¹ = a * (a⁻¹ * (t * a * t⁻¹)) := by group
        _ = a * 1 := by rw [hc1]
        _ = a := by group
    exact this
  have htC : t ∈ Subgroup.centralizer ((A ⊓ Subgroup.centralizer (B : Set G) :
      Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := htaB a ha
    have hta : t * a = a * t := by
      calc t * a = (t * a * t⁻¹) * t := by group
        _ = a * t := by rw [h]
    exact hta.symm
  have hzC : Subgroup.zpowers t ≤ Subgroup.centralizer
      ((A ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr htC
  have hker : P ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) = B :=
    inf_centralizer_inf_centralizer_eq_of_card_mul_eq hB hBcard hAP hneA
  rw [Subgroup.commutator_le]
  intro x hxP s hs
  have hxN : x ∈ Subgroup.normalizer ((A ⊓ Subgroup.centralizer (B : Set G) :
      Subgroup G) : Set G) := by
    have hxNA : x ∈ Subgroup.normalizer (A : Set G) := hPA hxP
    have hxCB : x ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hP.1.is_comm.comm ⟨b, hB hb⟩ ⟨x, hxP⟩)
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨hxNA, (Subgroup.centralizer (B : Set G)).le_normalizer hxCB⟩)
  have hsC : s ∈ Subgroup.centralizer
      ((A ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) := hzC hs
  have hsN : s ∈ Subgroup.normalizer (P : Set G) := Subgroup.zpowers_le.mpr htP hs
  have hcommP : ⁅x, s⁆ ∈ P := by
    have hPnP : (⁅P, Subgroup.normalizer (P : Set G)⁆ : Subgroup G) ≤ P :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (le_refl (Subgroup.normalizer (P : Set G)))
    exact hPnP (Subgroup.commutator_mem_commutator hxP hsN)
  have hcommC : ⁅x, s⁆ ∈ Subgroup.centralizer
      ((A ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : x⁻¹ * a * x ∈ A ⊓ Subgroup.centralizer (B : Set G) :=
      (Subgroup.mem_normalizer_iff''.mp hxN a).mp ha
    have hs_conj : s * (x⁻¹ * a * x) * s⁻¹ = x⁻¹ * a * x := by
      have hy := Subgroup.mem_centralizer_iff.mp hsC (x⁻¹ * a * x) ha'
      rw [← hy]
      group
    have hsa : s⁻¹ * a * s = a := by
      have hy := Subgroup.mem_centralizer_iff.mp hsC a ha
      rw [mul_assoc, hy, ← mul_assoc, inv_mul_cancel, one_mul]
    have hfix : ⁅x, s⁆ * a * ⁅x, s⁆⁻¹ = a := by
      calc ⁅x, s⁆ * a * ⁅x, s⁆⁻¹
          = x * s * x⁻¹ * (s⁻¹ * a * s) * x * s⁻¹ * x⁻¹ := by
            rw [commutatorElement_def]; group
        _ = x * s * x⁻¹ * a * x * s⁻¹ * x⁻¹ := by rw [hsa]
        _ = x * (s * (x⁻¹ * a * x) * s⁻¹) * x⁻¹ := by group
        _ = x * (x⁻¹ * a * x) * x⁻¹ := by rw [hs_conj]
        _ = a := by group
    calc a * ⁅x, s⁆ = (⁅x, s⁆ * a * ⁅x, s⁆⁻¹) * ⁅x, s⁆ := by rw [hfix]
      _ = ⁅x, s⁆ * a := by group
  exact hker ▸ Subgroup.mem_inf.mpr ⟨hcommP, hcommC⟩

theorem seven_nine_core {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {I P Z : Subgroup G} {t : G}
    (hI : IsElemAbelian 2 I) (hP : IsElemAbelian p P)
    (hPI : P ≤ Subgroup.normalizer (I : Set G)) (hA : ⁅I, P⁆ ≠ ⊥)
    (htI : t ∈ Subgroup.normalizer (I : Set G)) (htP : t ∈ Subgroup.normalizer (P : Set G))
    (hZP : Z ≤ P) (hZt : Z ≤ Subgroup.centralizer ({t} : Set G))
    (hZcard : Nat.card Z * p = Nat.card P)
    (hIt : ⁅I, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (Z : Set G))
    (hconj : ∀ B : Subgroup G, B ≤ P → Nat.card B * p = Nat.card P →
      ∃ g ∈ Subgroup.normalizer (I : Set G), g ∈ Subgroup.normalizer (P : Set G) ∧
        conjSubgroup B g ≠ Z ∧ ¬ ⁅P, Subgroup.zpowers t⁆ ≤ conjSubgroup B g) :
    False := by
  classical
  set A : Subgroup G := ⁅I, P⁆ with hA_def
  have hA_le_I : A ≤ I := by
    rw [hA_def]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hPI
  have hAab : IsMulCommutative ↥A :=
    IsMulCommutative.of_comm fun x y => by
      apply Subtype.ext
      simpa using congrArg Subtype.val
        (hI.1.is_comm.comm (⟨x, hA_le_I x.2⟩ : ↥I) ⟨y, hA_le_I y.2⟩)
  have hAe : IsElemAbelian 2 A := ⟨hAab, fun x hx => hI.2 x (hA_le_I hx)⟩
  have hPp : IsPGroup p P := fun y => ⟨1, Subtype.ext (by simpa using hP.2 y y.2)⟩
  have hPA : P ≤ Subgroup.normalizer (A : Set G) := by
    rw [hA_def]
    exact Subgroup.normalizer_commutator_ge_right I P
  have hAP : A ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
    rw [hA_def]
    exact commutator_inf_centralizer_right_eq_bot hp2 hI hPp hPI
  have hAne : A ≠ ⊥ := by
    simpa only [hA_def] using hA
  obtain ⟨B₀, hB₀P, hB₀card, hB₀ne⟩ :=
    exists_card_mul_eq_inf_centralizer_ne_bot hp2 hAe hP hPA hAne hAP
  obtain ⟨g, hgI, hgP, hgBZ, hgnot⟩ := hconj B₀ hB₀P hB₀card
  have hgA : g ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hA_def, Subgroup.map_commutator]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp hgI,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgP]
  set B : Subgroup G := conjSubgroup B₀ g with hB_def
  have hBP : B ≤ P := by
    intro x hx
    rw [hB_def, mem_conjSubgroup_iff] at hx
    exact (Subgroup.mem_normalizer_iff.mp hgP x).mpr (hB₀P hx)
  have hBcard : Nat.card B * p = Nat.card P := by
    have hc : Nat.card B = Nat.card B₀ := by
      rw [hB_def, conjSubgroup]
      exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g⁻¹))
    rw [hc, hB₀card]
  have hBZ : B ≠ Z := by
    rw [hB_def]
    exact hgBZ
  have hBne : A ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB₀ne
    have haA : (a : G) ∈ A := a.2.1
    have haC : (a : G) ∈ Subgroup.centralizer (B₀ : Set G) := a.2.2
    rw [Subgroup.mem_centralizer_iff] at haC
    have hgaA : g⁻¹ * (a : G) * g ∈ A :=
      (Subgroup.mem_normalizer_iff''.mp hgA (a : G)).mp haA
    have hgaC : g⁻¹ * (a : G) * g ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      rw [hB_def] at hb
      have hb₀ : g * b * g⁻¹ ∈ B₀ := mem_conjSubgroup_iff.mp hb
      have hcomm := haC (g * b * g⁻¹) hb₀
      calc b * (g⁻¹ * (a : G) * g)
          = g⁻¹ * ((g * b * g⁻¹) * (a : G)) * g := by group
        _ = g⁻¹ * ((a : G) * (g * b * g⁻¹)) * g := by rw [hcomm]
        _ = (g⁻¹ * (a : G) * g) * b := by group
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨g⁻¹ * (a : G) * g, Subgroup.mem_inf.mpr ⟨hgaA, hgaC⟩⟩, ?_⟩
    intro h
    apply ha1
    apply Subtype.ext
    have h1 : (a : G) = 1 := by
      have h2 : g⁻¹ * (a : G) * g = 1 := by
        simpa using congrArg Subtype.val h
      calc (a : G) = g * (g⁻¹ * (a : G) * g) * g⁻¹ := by group
        _ = g * 1 * g⁻¹ := by rw [h2]
        _ = 1 := by group
    simpa using h1
  have hcore := commutator_zpowers_le_of_inf_centralizer_ne_bot
    (B := B) hp2 hI hP hPI htI htP hZP hZt hZcard hIt hBP hBcard hBZ hBne
  exact hgnot (by rwa [hB_def] at hcore)

end CFSG.LocalAnalysis.WeakClosure81
