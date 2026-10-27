module

public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormGroup
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.Adapters.WholeGroupLayer
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

open scoped IsMulCommutative commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.B8

open CFSG CFSG.RankThree.GF2n.Smith81.OrthTN CFSG.LocalCores

section ThreeFactorLemmas

variable {H : Type*} [Group H]

theorem sup_eq_mul_of_comm {A B : Subgroup H} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup H :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← hc a' ha' b hb]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have h1 : a * b = b * a := hc a ha b hb
        calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [h1]
          _ = a⁻¹ * b⁻¹ := by group }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)
  exact fun x hx => hle hx

theorem threeFactors_sup (F : Fin 3 → Subgroup H) (hs : ∀ i, IsSimpleGroup ↥(F i))
    (hn : ∀ i, ∃ x ∈ F i, ∃ y ∈ F i, x * y ≠ y * x)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ F i, ∀ y ∈ F j, x * y = y * x) :
    ThreeFactors F (F 0 ⊔ F 1 ⊔ F 2) where
  le i := by
    fin_cases i
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  simple := hs
  nonab := hn
  comm := hc
  gen := by
    intro e he
    have hc2 : ∀ a ∈ F 0 ⊔ F 1, ∀ b ∈ F 2, a * b = b * a := by
      intro a ha b hb
      have hle : F 0 ⊔ F 1 ≤ Subgroup.centralizer (F 2 : Set H) :=
        sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
            (hc 0 2 (by decide) x hx y hy).symm)
          (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
            (hc 1 2 (by decide) x hx y hy).symm)
      exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
    obtain ⟨u, hu, c, hcm, rfl⟩ := sup_eq_mul_of_comm hc2 e he
    obtain ⟨a₀, ha₀, a₁, ha₁, rfl⟩ := sup_eq_mul_of_comm (hc 0 1 (by decide)) u hu
    exact ⟨a₀, ha₀, a₁, ha₁, c, hcm, rfl⟩

variable {A : Fin 3 → Subgroup H} {E : Subgroup H}

theorem threeFactors_inf_eq_bot (h : ThreeFactors A E) {i j : Fin 3} (hij : i ≠ j) :
    A i ⊓ A j = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact eq_one_of_mem_of_commute_of_isSimpleGroup (h.simple i) (h.nonab i) hx.1
    (fun y hy => h.comm i j hij y hy x hx.2)

theorem threeFactors_exists_le (h : ThreeFactors A E) {S : Subgroup H}
    (hS : ∀ i, ∀ x ∈ A i, ∀ s ∈ S, x * s * x⁻¹ ∈ S) {s : H} (hsS : s ∈ S) (hsE : s ∈ E)
    (hs1 : s ≠ 1) : ∃ i, A i ≤ S := by
  by_contra hne
  push Not at hne
  apply hs1
  refine h.eq_one hsE fun i x hx => ?_
  have hmem : s * x * s⁻¹ * x⁻¹ ∈ S ⊓ A i := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : x * s⁻¹ * x⁻¹ ∈ S := hS i x hx s⁻¹ (S.inv_mem hsS)
      have e1 : s * x * s⁻¹ * x⁻¹ = s * (x * s⁻¹ * x⁻¹) := by group
      rw [e1]
      exact S.mul_mem hsS h1
    · exact mul_mem (h.conj_mem i hsE hx) (inv_mem hx)
  have hbot : S ⊓ A i = ⊥ := by
    rcases eq_bot_or_eq_of_isSimpleGroup_of_normalized (inf_le_right : S ⊓ A i ≤ A i)
        (h.simple i) (fun b hb a ha => Subgroup.mem_inf.mpr
          ⟨hS i b hb a (Subgroup.mem_inf.mp ha).1,
            mul_mem (mul_mem hb (Subgroup.mem_inf.mp ha).2) (inv_mem hb)⟩) with h1 | h1
    · exact h1
    · exact absurd (inf_eq_right.mp h1) (hne i)
  rw [hbot, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hmem)

end ThreeFactorLemmas


section LayerFacts

variable {H : Type} [Group H] [Finite H]

theorem fitting_eq_bot (hF : ∀ A : Subgroup H, A.Normal → Group.IsNilpotent A → A = ⊥) :
    fittingSubgroup H = ⊥ :=
  hF _ inferInstance inferInstance

theorem centralizer_layer_eq_bot
    (hF : ∀ A : Subgroup H, A.Normal → Group.IsNilpotent A → A = ⊥) :
    Subgroup.centralizer (layer H : Set H) = ⊥ := by
  have hFit := fitting_eq_bot hF
  have h1 := CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup H
  rw [generalizedFitting.eq_sup, hFit, bot_sup_eq] at h1
  exact le_bot_iff.mp h1

theorem center_comp_trivial (hC : Subgroup.centralizer (layer H : Set H) = ⊥) {J : Subgroup H}
    (hJ : IsComponent J) {x : H} (hx : x ∈ J) (hc : ∀ y ∈ J, x * y = y * x) : x = 1 := by
  have hz : (⟨x, hx⟩ : J) ∈ Subgroup.center J :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2).symm
  have hmem := center_component_le_centralizer_layer hJ ⟨⟨x, hx⟩, hz, rfl⟩
  rw [hC, Subgroup.mem_bot] at hmem
  exact hmem

theorem exists_component (hC : Subgroup.centralizer (layer H : Set H) = ⊥) {x : H}
    (hx : x ≠ 1) : ∃ J : Subgroup H, IsComponent J := by
  by_contra hne
  push Not at hne
  have hbot := layer_eq_bot_of_forall hne
  apply hx
  have hx' : x ∈ Subgroup.centralizer (layer H : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hbot, Subgroup.coe_bot, Set.mem_singleton_iff] at hh
    rw [hh, one_mul, mul_one]
  rw [hC] at hx'
  exact Subgroup.mem_bot.mp hx'

theorem inf_comp_ne_bot {L : Subgroup H} (hLsq : ∀ x ∈ L, x * x = 1) (hLi : ¬ 2 ∣ L.index)
    {J : Subgroup H} (hJ : IsComponent J) : J ⊓ L ≠ ⊥ := by
  have hLp : IsPGroup 2 L := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hLsq x x.2)⟩
  have hS : CFSG.Quasithin.IsSylowIn 2 L ⊤ :=
    ⟨le_top, hLp, by rwa [Subgroup.relIndex_top_right]⟩
  haveI : (layer H).Characteristic := layer_characteristic
  have hS1 := hS.inf_normal (N := layer H) le_top inferInstance
  obtain ⟨hJE, hJN⟩ := components_normal_in_layer hJ
  have hS2 := hS1.inf_normal hJE hJN
  intro hbot
  have hbot' : L ⊓ layer H ⊓ J = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have : x ∈ J ⊓ L := ⟨hx.2, hx.1.1⟩
    rwa [hbot] at this
  have h2 := hS2.not_dvd_relIndex
  rw [hbot', Subgroup.relIndex_bot_left] at h2
  have hodd : Odd (Nat.card J) := Nat.odd_iff.mpr (by omega)
  haveI := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  haveI : Group.IsPerfect ↥J := hJ.1.1
  haveI : Nontrivial ↥J := isQuasisimple_nontrivial hJ.1
  exact Group.IsPerfect.not_isSolvable ↥J inferInstance

def conjS (u : H) (J : Subgroup H) : Subgroup H := J.map (MulAut.conj u).toMonoidHom

theorem mem_conjS {u : H} {J : Subgroup H} {y : H} : y ∈ conjS u J ↔ u⁻¹ * y * u ∈ J := by
  unfold conjS
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem isComponent_conjS {u : H} {J : Subgroup H} (hJ : IsComponent J) :
    IsComponent (conjS u J) :=
  isComponent_map_mulEquiv (MulAut.conj u) hJ

theorem comp_normalized_by_L {L : Subgroup H}
    (hC : Subgroup.centralizer (layer H : Set H) = ⊥)
    (hLab : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) (hLsq : ∀ x ∈ L, x * x = 1)
    (hLi : ¬ 2 ∣ L.index) {J : Subgroup H} (hJ : IsComponent J) {u : H} (hu : u ∈ L) :
    ∀ y, y ∈ J ↔ u * y * u⁻¹ ∈ J := by
  have hconj : conjS u J = J := by
    by_contra hne
    have hJ' := isComponent_conjS (u := u) hJ
    have hcomm := (distinct_components_commute hJ hJ').resolve_left (fun h => hne h.symm)
    obtain ⟨⟨w, hwJL⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (inf_comp_ne_bot hLsq hLi hJ)
    have hwJ : w ∈ J := hwJL.1
    have hwL : w ∈ L := hwJL.2
    have hwc : u⁻¹ * w * u = w := by
      have := hLab u hu w hwL
      calc u⁻¹ * w * u = u⁻¹ * (w * u) := by group
        _ = u⁻¹ * (u * w) := by rw [this]
        _ = w := by group
    have hwJ' : w ∈ conjS u J := by
      rw [mem_conjS, hwc]
      exact hwJ
    apply hw1
    refine Subtype.ext (center_comp_trivial hC hJ hwJ fun y hy => ?_)
    have h1 : ⁅y, w⁆ ∈ ⁅J, conjS u J⁆ := Subgroup.commutator_mem_commutator hy hwJ'
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  intro y
  have := mem_conjS (u := u) (J := J) (y := u * y * u⁻¹)
  rw [hconj] at this
  have e : u⁻¹ * (u * y * u⁻¹) * u = y := by group
  rw [e] at this
  exact this.symm

def compStab (H : Type) [Group H] : Subgroup H :=
  ⨅ J : {J : Subgroup H // IsComponent J}, Subgroup.normalizer (J.1 : Set H)

theorem mem_compStab {h : H} :
    h ∈ compStab H ↔ ∀ J : Subgroup H, IsComponent J → ∀ y, y ∈ J ↔ h * y * h⁻¹ ∈ J := by
  simp only [compStab, Subgroup.mem_iInf, Subgroup.mem_normalizer_iff, Subtype.forall]

instance compStab_normal : (compStab H).Normal :=
  ⟨fun k hk x => by
    rw [mem_compStab] at hk ⊢
    intro J hJ y
    have hJ' := isComponent_conjS (u := x⁻¹) hJ
    have h1 := hk _ hJ' (x⁻¹ * y * x)
    simp only [mem_conjS, inv_inv] at h1
    have e1 : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    have e2 : x * (k * (x⁻¹ * y * x) * k⁻¹) * x⁻¹ = x * k * x⁻¹ * y * (x * k * x⁻¹)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1⟩

theorem compStab_eq_top (hperf : Group.IsPerfect H) {L : Subgroup H} (hLK : L ≤ compStab H)
    (hLi : ¬ 2 ∣ L.index) : compStab H = ⊤ := by
  have hidx : ¬ 2 ∣ (compStab H).index := fun h => hLi (h.trans (Subgroup.index_dvd_of_le hLK))
  haveI : Group.IsPerfect (H ⧸ compStab H) := inferInstance
  have hodd : Odd (Nat.card (H ⧸ compStab H)) := Nat.odd_iff.mpr (by
    have : (compStab H).index = Nat.card (H ⧸ compStab H) := rfl
    omega)
  haveI := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  by_contra hne
  haveI : Nontrivial (H ⧸ compStab H) := by
    have h1 : (compStab H).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
    have h2 : (compStab H).index = Nat.card (H ⧸ compStab H) := rfl
    have h3 : 1 < Nat.card (H ⧸ compStab H) := by
      have := Nat.card_pos (α := H ⧸ compStab H)
      omega
    exact Finite.one_lt_card_iff_nontrivial.mp h3
  exact Group.IsPerfect.not_isSolvable (H ⧸ compStab H) inferInstance

theorem comp_normal (hperf : Group.IsPerfect H)
    (hC : Subgroup.centralizer (layer H : Set H) = ⊥) {L : Subgroup H}
    (hLab : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) (hLsq : ∀ x ∈ L, x * x = 1)
    (hLi : ¬ 2 ∣ L.index) {J : Subgroup H} (hJ : IsComponent J) : J.Normal := by
  have hLK : L ≤ compStab H := fun u hu => by
    rw [mem_compStab]
    intro J' hJ' y
    exact comp_normalized_by_L hC hLab hLsq hLi hJ' hu y
  have htop := compStab_eq_top hperf hLK hLi
  refine ⟨fun x hx h => ?_⟩
  have hh : h ∈ compStab H := by rw [htop]; exact Subgroup.mem_top h
  exact (mem_compStab.mp hh J hJ x).mp hx

end LayerFacts


section Cycle

variable {H : Type*} [Group H] {A : Fin 3 → Subgroup H} {E : Subgroup H}

theorem exists_odd_pow_mem {L : Subgroup H} (hLi : ¬ 2 ∣ L.index) {g : H}
    (hg : g ∈ Subgroup.normalizer (L : Set H)) : ∃ k : ℕ, Odd k ∧ g ^ k ∈ L := by
  haveI : (L.subgroupOf (Subgroup.normalizer (L : Set H))).Normal :=
    Subgroup.normal_in_normalizer
  refine ⟨(L.subgroupOf (Subgroup.normalizer (L : Set H))).index, ?_, ?_⟩
  · have hdvd : (L.subgroupOf (Subgroup.normalizer (L : Set H))).index ∣ L.index :=
      Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer
    have : ¬ 2 ∣ (L.subgroupOf (Subgroup.normalizer (L : Set H))).index :=
      fun h => hLi (h.trans hdvd)
    exact Nat.odd_iff.mpr (by omega)
  · have := Subgroup.pow_index_mem (L.subgroupOf (Subgroup.normalizer (L : Set H))) ⟨g, hg⟩
    simpa using Subgroup.mem_subgroupOf.mp this

theorem exists_cycle (h : ThreeFactors A E) {g : H}
    (hg : ∀ x ∈ E, g * x * g⁻¹ ∈ E) (hg' : ∀ x ∈ E, g⁻¹ * x * g ∈ E)
    {a : H} (ha : a ∈ A 0) (ha1 : a ≠ 1) (hag : g * a * g⁻¹ ∈ A 1)
    {k : ℕ} (hk : Odd k) (hgk : g ^ k ∈ E) :
    ∃ π : Equiv.Perm (Fin 3), (∀ (i : Fin 3) (x : H), x ∈ A i ↔ g * x * g⁻¹ ∈ A (π i)) ∧
      π 0 = 1 ∧ π 1 = 2 ∧ π 2 = 0 := by
  obtain ⟨π, hπ⟩ := h.exists_perm g hg hg'
  have h0 : π 0 = 1 := by
    by_contra hne
    have hmem : g * a * g⁻¹ ∈ A (π 0) ⊓ A 1 := ⟨(hπ 0 a).mp ha, hag⟩
    rw [threeFactors_inf_eq_bot h hne, Subgroup.mem_bot, conj_eq_one_iff] at hmem
    exact ha1 hmem
  have hpow : ∀ m : ℕ, ∀ (i : Fin 3) (x : H),
      x ∈ A i ↔ g ^ m * x * (g ^ m)⁻¹ ∈ A ((π ^ m) i) := by
    intro m
    induction m with
    | zero => intro i x; simp
    | succ m ih =>
      intro i x
      have e1 : g ^ (m + 1) * x * (g ^ (m + 1))⁻¹ = g * (g ^ m * x * (g ^ m)⁻¹) * g⁻¹ := by
        group
      rw [e1, pow_succ', Equiv.Perm.mul_apply, ← hπ, ← ih]
  have hπk : (π ^ k) 0 = 0 := by
    by_contra hne
    have h1 := (hpow k 0 a).mp ha
    have h2 := (h.conj_iff 0 hgk a).mp ha
    have hmem : g ^ k * a * (g ^ k)⁻¹ ∈ A ((π ^ k) 0) ⊓ A 0 := ⟨h1, h2⟩
    rw [threeFactors_inf_eq_bot h hne, Subgroup.mem_bot, conj_eq_one_iff] at hmem
    exact ha1 hmem
  have hne0 : π 1 ≠ 0 := by
    intro h10
    have h2 : (π ^ 2) 0 = 0 := by
      rw [pow_two, Equiv.Perm.mul_apply, h0, h10]
    have h2m : ∀ m : ℕ, (π ^ (2 * m)) 0 = 0 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [show 2 * (m + 1) = 2 + 2 * m by ring, pow_add, Equiv.Perm.mul_apply, ih, h2]
    obtain ⟨m, rfl⟩ := hk
    have : (π ^ (2 * m + 1)) 0 = 1 := by
      rw [pow_succ', Equiv.Perm.mul_apply, h2m, h0]
    rw [this] at hπk
    exact absurd hπk (by decide)
  have hne1 : π 1 ≠ 1 := by
    intro h11
    have := π.injective (h11.trans h0.symm)
    exact absurd this (by decide)
  have h1 : π 1 = 2 := by
    rcases (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) (π 1) with h | h | h
    · exact absurd h hne0
    · exact absurd h hne1
    · exact h
  have h2 : π 2 = 0 := by
    have hne2 : π 2 ≠ 1 := fun h' => absurd (π.injective (h'.trans h0.symm)) (by decide)
    have hne2' : π 2 ≠ 2 := fun h' => absurd (π.injective (h'.trans h1.symm)) (by decide)
    rcases (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) (π 2) with h | h | h
    · exact h
    · exact absurd h hne2
    · exact absurd h hne2'
  exact ⟨π, hπ, h0, h1, h2⟩

end Cycle

section Core

theorem core {H : Type} [Group H] [Finite H]
    (hWalter : ∀ (D : Type) [Group D] [Finite D] [IsSimpleGroup D], (∃ a b : D, a * b ≠ b * a) →
      ∀ P : Sylow 2 D, IsMulCommutative ↥P → 16 ≤ Nat.card ↥P →
        ∀ i : D, i * i = 1 → i ≠ 1 → IsPGroup 2 ↥(Subgroup.centralizer ({i} : Set D)))
    (hperf : Group.IsPerfect H)
    (hF : ∀ A : Subgroup H, A.Normal → Group.IsNilpotent A → A = ⊥)
    (L : Subgroup H) (hLi : ¬ 2 ∣ L.index) (hL16 : 16 ≤ Nat.card ↥L)
    (hLab : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) (hLsq : ∀ x ∈ L, x * x = 1)
    (F : Fin 3 → Subgroup H) (hs : ∀ i, IsSimpleGroup ↥(F i))
    (hn : ∀ i, ∃ x ∈ F i, ∃ y ∈ F i, x * y ≠ y * x)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ F i, ∀ y ∈ F j, x * y = y * x)
    (hLE : L ≤ F 0 ⊔ F 1 ⊔ F 2)
    (hNorm : ∀ n ∈ Subgroup.normalizer (L : Set H), ∀ x ∈ F 0 ⊔ F 1 ⊔ F 2,
      n * x * n⁻¹ ∈ F 0 ⊔ F 1 ⊔ F 2)
    (g a : H) (hg : g ∈ Subgroup.normalizer (L : Set H)) (haL : a ∈ L) (haF : a ∈ F 0)
    (ha1 : a ≠ 1) (hag : g * a * g⁻¹ ∈ F 1) : False := by
  have hTF := threeFactors_sup F hs hn hc
  have hC := centralizer_layer_eq_bot hF
  obtain ⟨J, hJ⟩ := exists_component hC ha1
  have hJn : J.Normal := comp_normal hperf hC hLab hLsq hLi hJ
  obtain ⟨⟨w, hwJL⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (inf_comp_ne_bot hLsq hLi hJ)
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  obtain ⟨i₀, hi₀⟩ := threeFactors_exists_le hTF (S := J)
    (fun i x _ s hs => hJn.conj_mem s hs x) hwJL.1 (hLE hwJL.2) hw1'
  have hg' : g⁻¹ ∈ Subgroup.normalizer (L : Set H) := inv_mem hg
  obtain ⟨k, hk, hgk⟩ := exists_odd_pow_mem hLi hg
  obtain ⟨π, hπ, h0, h1, h2⟩ := exists_cycle hTF (hNorm g hg)
    (fun x hx => by simpa using hNorm g⁻¹ hg' x hx) haF ha1 hag hk (hLE hgk)
  have hprop : ∀ i, F i ≤ J → F (π i) ≤ J := by
    intro i hi y hy
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    have hy' : g⁻¹ * y * g ∈ F i := (hπ i (g⁻¹ * y * g)).mpr (by rw [e]; exact hy)
    have := hJn.conj_mem _ (hi hy') g
    rwa [e] at this
  have p0 : F 0 ≤ J → F 1 ≤ J := by
    have := hprop 0
    rwa [h0] at this
  have p1 : F 1 ≤ J → F 2 ≤ J := by
    have := hprop 1
    rwa [h1] at this
  have p2 : F 2 ≤ J → F 0 ≤ J := by
    have := hprop 2
    rwa [h2] at this
  have hall : F 0 ≤ J ∧ F 1 ≤ J ∧ F 2 ≤ J := by
    fin_cases i₀
    · exact ⟨hi₀, p0 hi₀, p1 (p0 hi₀)⟩
    · exact ⟨p2 (p1 hi₀), hi₀, p1 hi₀⟩
    · exact ⟨p2 hi₀, p0 (p2 hi₀), hi₀⟩
  obtain ⟨hJ0, hJ1, hJ2⟩ := hall
  have hLJ : L ≤ J := hLE.trans (sup_le (sup_le hJ0 hJ1) hJ2)
  have haJ : a ∈ J := hLJ haL
  have hZ : Subgroup.center ↥J = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine center_comp_trivial hC hJ x.2 fun y hy => ?_
    have := Subgroup.mem_center_iff.mp hx ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm
  haveI hJsimple : IsSimpleGroup ↥J := by
    have e : ↥J ⧸ Subgroup.center ↥J ≃* ↥J :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact (MulEquiv.isSimpleGroup_congr e).mp hJ.1.2.1
  have hnab : ∃ x y : ↥J, x * y ≠ y * x := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hn 0
    exact ⟨⟨x, hJ0 hx⟩, ⟨y, hJ0 hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  have hLp : IsPGroup 2 L := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hLsq x x.2)⟩
  have hsyl : CFSG.Quasithin.IsSylowIn 2 L J :=
    ⟨hLJ, hLp, fun hd => hLi (hd.trans (Subgroup.relIndex_dvd_index_of_le hLJ))⟩
  let P : Sylow 2 ↥J := hsyl.toSylow
  have hPc : IsMulCommutative ↥(P : Subgroup ↥J) :=
    ⟨⟨fun x y => Subtype.ext (Subtype.ext (hLab _ (Subgroup.mem_subgroupOf.mp x.2) _
      (Subgroup.mem_subgroupOf.mp y.2)))⟩⟩
  have hPcard : 16 ≤ Nat.card ↥(P : Subgroup ↥J) := by
    have : Nat.card ↥(P : Subgroup ↥J) = Nat.card ↥L :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLJ).toEquiv
    omega
  have hcent := hWalter ↥J hnab P hPc hPcard ⟨a, haJ⟩ (Subtype.ext (hLsq a haL))
    (fun h => ha1 (congrArg Subtype.val h))
  have hF1J : F 1 ≤ J := hJ1
  have hle : (F 1).subgroupOf J ≤ Subgroup.centralizer ({(⟨a, haJ⟩ : ↥J)} : Set ↥J) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    rw [Set.mem_singleton_iff] at hi
    subst hi
    exact Subtype.ext (hc 0 1 (by decide) a haF x (Subgroup.mem_subgroupOf.mp hx))
  have hpg : IsPGroup 2 ↥(F 1) :=
    (hcent.to_le hle).of_equiv (Subgroup.subgroupOfEquivOfLe hF1J)
  haveI : IsSimpleGroup ↥(F 1) := hs 1
  haveI : Finite ↥(F 1) := inferInstance
  haveI : Group.IsNilpotent ↥(F 1) := hpg.isNilpotent
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr (inferInstance : Group.IsSolvable ↥(F 1))
  obtain ⟨x, hx, y, hy, hxy⟩ := hn 1
  exact hxy (congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩))

end Core

end CFSG.RankThree.GF2n.Smith81.Smith23E1.B8
