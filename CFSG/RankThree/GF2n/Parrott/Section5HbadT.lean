module

public import CFSG.RankThree.GF2n.Parrott.Section5HbadTJ
public import CFSG.RankThree.GF2n.Parrott.Section5LocalW
public import CFSG.RankThree.GF2n.Parrott.Section5ChoiceT1
public import CFSG.RankThree.GF2n.Parrott.Section5ChoiceS0

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

private theorem card_CJ_le_conj {g y : G} (hg : g ∈ H z) :
    Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤
      Nat.card ↥(J z ⊓ centralizer ({g * y * g⁻¹} : Set G)) := by
  have hHJ : H z ≤ normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  refine Nat.card_le_card_of_injective
    (fun x : ↥(J z ⊓ centralizer ({y} : Set G)) =>
      (⟨g * (x : G) * g⁻¹, ?_⟩ : ↥(J z ⊓ centralizer ({g * y * g⁻¹} : Set G)))) ?_
  · refine Subgroup.mem_inf.mpr
      ⟨(mem_normalizer_iff.mp (hHJ hg) (x : G)).mp (Subgroup.mem_inf.mp x.2).1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : (x : G) * y = y * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2
    calc g * (x : G) * g⁻¹ * (g * y * g⁻¹) = g * ((x : G) * y) * g⁻¹ := by group
      _ = g * (y * (x : G)) * g⁻¹ := by rw [hcomm]
      _ = (g * y * g⁻¹) * (g * (x : G) * g⁻¹) := by group
  · intro x x' hxx
    have hval : g * (x : G) * g⁻¹ = g * (x' : G) * g⁻¹ :=
      congrArg (fun t : ↥(J z ⊓ centralizer ({g * y * g⁻¹} : Set G)) => (t : G)) hxx
    refine Subtype.ext ?_
    calc (x : G) = g⁻¹ * (g * (x : G) * g⁻¹) * g := by group
      _ = g⁻¹ * (g * (x' : G) * g⁻¹) * g := by rw [hval]
      _ = (x' : G) := by group

private theorem map_conj_le_H_C {g y : G} (hg : g ∈ H z) {B : Subgroup G}
    (hBC : B ≤ H z ⊓ centralizer ({y} : Set G)) :
    B.map (MulAut.conj g).toMonoidHom ≤ H z ⊓ centralizer ({g * y * g⁻¹} : Set G) := by
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨hbH, hbc⟩ := Subgroup.mem_inf.mp (hBC hb)
  refine Subgroup.mem_inf.mpr
    ⟨(H z).mul_mem ((H z).mul_mem hg hbH) ((H z).inv_mem hg), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcomm : (b : G) * y = y * (b : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hbc
  calc g * (b : G) * g⁻¹ * (g * y * g⁻¹) = g * ((b : G) * y) * g⁻¹ := by group
    _ = g * (y * (b : G)) * g⁻¹ := by rw [hcomm]
    _ = (g * y * g⁻¹) * (g * (b : G) * g⁻¹) := by group

private theorem map_conj_normalized {g y : G} (hg : g ∈ H z) {B : Subgroup G}
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B) :
    ∀ c ∈ H z ⊓ centralizer ({g * y * g⁻¹} : Set G),
      ∀ b ∈ B.map (MulAut.conj g).toMonoidHom,
        c * b * c⁻¹ ∈ B.map (MulAut.conj g).toMonoidHom := by
  rintro c hc _ ⟨b, hb, rfl⟩
  obtain ⟨hcH, hcc⟩ := Subgroup.mem_inf.mp hc
  have hgi : (g : G)⁻¹ ∈ H z := (H z).inv_mem hg
  have hc' : (g : G)⁻¹ * c * (g : G) ∈ H z ⊓ centralizer ({y} : Set G) := by
    refine Subgroup.mem_inf.mpr
      ⟨(H z).mul_mem ((H z).mul_mem hgi hcH) hg, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcy : c * (g * y * g⁻¹) = (g * y * g⁻¹) * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hcc
    calc (g : G)⁻¹ * c * g * y = (g : G)⁻¹ * (c * (g * y * g⁻¹)) * g := by group
      _ = (g : G)⁻¹ * ((g * y * g⁻¹) * c) * g := by rw [hcy]
      _ = y * ((g : G)⁻¹ * c * g) := by group
  refine Subgroup.mem_map.mpr ⟨_, hBn _ hc' b hb, ?_⟩
  show g * ((g : G)⁻¹ * c * g * b * ((g : G)⁻¹ * c * g)⁻¹) * g⁻¹ =
    c * (g * b * g⁻¹) * c⁻¹
  group

private theorem exists_J_conj_mem_of_conj_case {g y : G} (hg : g ∈ H z) {B : Subgroup G}
    (hcase : ∃ c' ∈ J z, c' * (g * y * g⁻¹) * c'⁻¹ ∈ B.map (MulAut.conj g).toMonoidHom ∧
      c' * (g * y * g⁻¹) * c'⁻¹ ≠ g * y * g⁻¹) :
    ∃ c ∈ J z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y := by
  obtain ⟨c', hc'J, hc'B, hc'ne⟩ := hcase
  obtain ⟨b, hbB, hbeq⟩ := Subgroup.mem_map.mp hc'B
  have hHJ : H z ≤ normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  have hgi : (g : G)⁻¹ ∈ H z := (H z).inv_mem hg
  refine ⟨(g : G)⁻¹ * c' * g, ?_, ?_, ?_⟩
  · simpa using (mem_normalizer_iff.mp (hHJ hgi) c').mp hc'J
  · have hconj : (g : G)⁻¹ * c' * g * y * ((g : G)⁻¹ * c' * g)⁻¹ =
        (g : G)⁻¹ * (c' * (g * y * g⁻¹) * c'⁻¹) * g := by group
    rw [hconj, ← hbeq]
    have hb_eq : (g : G)⁻¹ *
        ((MulEquiv.toMonoidHom (MulAut.conj (g : G))) b) * (g : G) = b := by
      change (g : G)⁻¹ * ((MulAut.conj (g : G)) b) * (g : G) = b
      rw [MulAut.conj_apply]
      group
    rw [hb_eq]
    exact hbB
  · intro heq
    apply hc'ne
    calc c' * (g * y * g⁻¹) * c'⁻¹ =
        g * ((g : G)⁻¹ * c' * g * y * ((g : G)⁻¹ * c' * g)⁻¹) * g⁻¹ := by group
      _ = g * y * g⁻¹ := by rw [heq]

private theorem exists_conj_y_data {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {y : G} (hyH : y ∈ H z) (hy : orderOf y = 2)
    (hbad : ∀ c ∈ H z,
      c * y * c⁻¹ ∉ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    {g : ↥(H z)} {a : A45} (hgq : qH (z := z) D g = a)
    (ha : a * qH (z := z) D ⟨y, hyH⟩ * a⁻¹ = tA) :
    ∃ (y' : G) (hy'H : y' ∈ H z),
      y' = (g : G) * y * (g : G)⁻¹ ∧ orderOf y' = 2 ∧
        qH (z := z) D ⟨y', hy'H⟩ = tA ∧
        (∀ c ∈ H z,
          c * y' * c⁻¹ ∉ lemma54T₂ D
            ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) := by
  refine ⟨(g : G) * y * (g : G)⁻¹, ?_, rfl, ?_, ?_, ?_⟩
  · exact (H z).mul_mem ((H z).mul_mem g.2 hyH) ((H z).inv_mem g.2)
  · rw [show orderOf ((g : G) * y * (g : G)⁻¹) = orderOf y from
      orderOf_injective (MulAut.conj (g : G)).toMonoidHom
        (MulAut.conj (g : G)).injective y]
    exact hy
  · have heq : (⟨(g : G) * y * (g : G)⁻¹, ((H z).mul_mem
        ((H z).mul_mem g.2 hyH) ((H z).inv_mem g.2))⟩ : ↥(H z)) =
        g * ⟨y, hyH⟩ * g⁻¹ := Subtype.ext rfl
    rw [heq, map_mul, map_mul, map_inv, hgq]
    exact ha
  · intro c hc
    have hcg : c * (g : G) ∈ H z := (H z).mul_mem hc g.2
    have hb := hbad (c * (g : G)) hcg
    rwa [show c * ((g : G) * y * (g : G)⁻¹) * c⁻¹ =
      (c * (g : G)) * y * (c * (g : G))⁻¹ by group]

private theorem exists_conj_B_data {y : G} {g : ↥(H z)} {B : Subgroup G}
    (hBC : B ≤ H z ⊓ centralizer ({y} : Set G))
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    (hyB : y ∈ B) (hzB : z ∉ B)
    (hcard : Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B) {y' : G}
    (hyj : y' = (g : G) * y * (g : G)⁻¹) :
    ∃ B' : Subgroup G,
      B' = B.map (MulAut.conj (g : G)).toMonoidHom ∧
      B' ≤ H z ⊓ centralizer ({y'} : Set G) ∧
      (∀ c ∈ H z ⊓ centralizer ({y'} : Set G), ∀ b ∈ B', c * b * c⁻¹ ∈ B') ∧
      y' ∈ B' ∧ z ∉ B' ∧
      Nat.card ↥(J z ⊓ centralizer ({y'} : Set G)) ≤ Nat.card B' := by
  have hg : (g : G) ∈ H z := g.2
  refine ⟨B.map (MulAut.conj (g : G)).toMonoidHom, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hyj]
    exact map_conj_le_H_C (z := z) (g := (g : G)) (y := y) hg hBC
  · rw [hyj]
    exact map_conj_normalized (z := z) (g := (g : G)) (y := y) hg hBn
  · refine Subgroup.mem_map.mpr ⟨y, hyB, ?_⟩
    rw [hyj]
    change (MulAut.conj (g : G)) y = (g : G) * y * (g : G)⁻¹
    rw [MulAut.conj_apply]
  · intro hz
    obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp hz
    apply hzB
    have hb_eq : b = z := by
      calc b = (g : G)⁻¹ *
            ((MulEquiv.toMonoidHom (MulAut.conj (g : G))) b) * (g : G) := by
            change b = (g : G)⁻¹ * ((MulAut.conj (g : G)) b) * (g : G)
            rw [MulAut.conj_apply]; group
        _ = (g : G)⁻¹ * z * (g : G) := by rw [hbeq]
        _ = z := by
            have hcomm : (g : G)⁻¹ * z = z * (g : G)⁻¹ :=
              Subgroup.mem_centralizer_singleton_iff.mp ((H z).inv_mem g.2)
            rw [hcomm, mul_assoc, inv_mul_cancel, mul_one]
    rwa [hb_eq] at hb
  · rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective]
    have hle : Nat.card ↥(J z ⊓ centralizer ({y'} : Set G)) ≤
        Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) := by
      have h := card_CJ_le_conj (z := z) (g := (g : G)⁻¹) ((H z).inv_mem hg) (y := y')
      rwa [show (g : G)⁻¹ * y' * ((g : G)⁻¹)⁻¹ = y from by
        rw [hyj]; group] at h
    exact hle.trans hcard

theorem exists_J_conj_mem_of_isConj_tA_of_forall_conj_not_mem_lemma54T₂
    (h : Tim79a.ParrottHyp z)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {y : G} (hyH : y ∈ H z) (hy : orderOf y = 2)
    (hcls : IsConj (qH (z := z) D ⟨y, hyH⟩) tA)
    (hbad : ∀ c ∈ H z,
      c * y * c⁻¹ ∉ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (B : Subgroup G) (hBC : B ≤ H z ⊓ centralizer ({y} : Set G))
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    (hyB : y ∈ B) (hzB : z ∉ B)
    (hcard : Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B) :
    ∃ c ∈ J z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y := by
  classical
  obtain ⟨a, ha⟩ := isConj_iff.mp hcls
  obtain ⟨g, hgq⟩ := qH_surjective D a
  obtain ⟨y', hy'H, hyj, hy'ord, hqy', hbad'⟩ :=
    exists_conj_y_data (z := z) (D := D) hq₂ hyH hy hbad hgq ha
  obtain ⟨B', hB'eq, hBC', hBn', hyB', hzB', hcard'⟩ :=
    exists_conj_B_data (z := z) (g := g) (y := y) hBC hBn hyB hzB hcard hyj
  obtain ⟨c', hc'J, hc'B, hc'ne⟩ :=
    exists_J_conj_mem_of_qH_eq_tA (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hy'H hy'ord
      hqy' hbad' B' hBC' hBn' hyB' hzB' hcard'
  rw [hB'eq, hyj] at hc'B
  rw [hyj] at hc'ne
  exact exists_J_conj_mem_of_conj_case (z := z) (g := (g : G)) g.2 ⟨c', hc'J, hc'B, hc'ne⟩

end CFSG.RankThree.GF2n.Parrott
