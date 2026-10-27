module

public import CFSG.Quasithin.Background.A312SporE8
public import CFSG.Quasithin.Background.A312SporShapesCheck
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312ExtShapesExtra
public import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.A312S

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat

theorem mem_pCoreOf_of_fixes {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
    {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (C : LatCtx Γ n Lab) {j : ℕ}
    (hj : j < C.J) (hodd : C.D.Om[j]!.lbl.size % 2 = 1) {z : Γ}
    (h : ∀ x ∈ C.D.Om[j]!.lbl.toList, C.A.act (tab n z).toArray x = x) :
    z ∈ CFSG.Open.pCoreOf 2 (C.Y j) := by
  rw [C.core_eq hj hodd, C.mem_tupStab hj]
  exact h

theorem fixes_of_fixLabs {t : Array ℕ} {labs : List (List ℕ)} (h : fixLabs t labs = true) :
    ∀ x ∈ labs, ptLab.act t x = x := fun x hx => beq_iff_eq.mp (List.all_eq_true.mp h x hx)

theorem pCoreOf_eq_closure_of_fixes {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ}
    [MulAction Γ (Fin n)] {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]
    (C : LatCtx Γ n Lab) {j : ℕ} (hj : j < C.J) (hodd : C.D.Om[j]!.lbl.size % 2 = 1)
    (gens : List Γ)
    (hfix : ∀ g ∈ gens, ∀ x ∈ C.D.Om[j]!.lbl.toList, C.A.act (tab n g).toArray x = x)
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (C.Y j)) ≤ Nat.card (Subgroup.closure {x | x ∈ gens})) :
    CFSG.Open.pCoreOf 2 (C.Y j) = Subgroup.closure {x | x ∈ gens} := by
  have hle : Subgroup.closure {x | x ∈ gens} ≤ CFSG.Open.pCoreOf 2 (C.Y j) :=
    (Subgroup.closure_le _).mpr fun g hg => mem_pCoreOf_of_fixes C hj hodd (hfix g hg)
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

section NormalCore

variable {Γ : Type} [Group Γ]

theorem card_of_isPSL32 {X : Type} [Group X] (h : IsPSL 3 2 1 X) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

end NormalCore

section Central

variable {G : Type} [Group G]

theorem oneZ_mul {z a b : G} (hz : z * z = 1) (ha : a = 1 ∨ a = z) (hb : b = 1 ∨ b = z) :
    a * b = 1 ∨ a * b = z := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · left; rw [mul_one]
  · right; rw [one_mul]
  · right; rw [mul_one]
  · left; exact hz

theorem oneZ_inv {z a : G} (hz : z * z = 1) (ha : a = 1 ∨ a = z) : a⁻¹ = 1 ∨ a⁻¹ = z := by
  rcases ha with rfl | rfl
  · left; rw [inv_one]
  · right; exact inv_eq_of_mul_eq_one_right hz

theorem oneZ_comm {z a x : G} (ha : a = 1 ∨ a = z) (hx : x * z = z * x) : a * x = x * a := by
  rcases ha with rfl | rfl
  · rw [one_mul, mul_one]
  · exact hx.symm

theorem comm_oneZ_closure {z y : G} {s : Set G} (hz : z * z = 1)
    (hzc : ∀ x ∈ Subgroup.closure s, x * z = z * x) (hyz : y * z = z * y)
    (hs : ∀ x ∈ s, ∃ ε, (ε = 1 ∨ ε = z) ∧ x * y = ε * (y * x)) :
    ∀ x ∈ Subgroup.closure s, ∃ ε, (ε = 1 ∨ ε = z) ∧ x * y = ε * (y * x) := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => exact ⟨1, Or.inl rfl, by rw [one_mul, mul_one, one_mul]⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨εa, hεa, hay⟩ := iha
    obtain ⟨εb, hεb, hby⟩ := ihb
    have hεba : εb * a = a * εb := oneZ_comm hεb (hzc a ha)
    refine ⟨εb * εa, oneZ_mul hz hεb hεa, ?_⟩
    calc a * b * y = a * (b * y) := mul_assoc a b y
      _ = a * (εb * (y * b)) := by rw [hby]
      _ = (εb * a) * (y * b) := by rw [hεba, mul_assoc]
      _ = εb * (a * y) * b := by simp only [mul_assoc]
      _ = εb * (εa * (y * a)) * b := by rw [hay]
      _ = εb * εa * (y * (a * b)) := by simp only [mul_assoc]
  | inv a ha iha =>
    obtain ⟨ε, hε, hay⟩ := iha
    have hε2 : ε * ε = 1 := by
      rcases hε with rfl | rfl
      · rw [mul_one]
      · exact hz
    have hεa : ε * a⁻¹ = a⁻¹ * ε := by
      have h1 := oneZ_comm hε (hzc a ha)
      calc ε * a⁻¹ = a⁻¹ * (a * ε) * a⁻¹ := by group
        _ = a⁻¹ * (ε * a) * a⁻¹ := by rw [h1]
        _ = a⁻¹ * ε := by group
    refine ⟨ε, hε, ?_⟩
    have h2 : y * a⁻¹ = ε * (a⁻¹ * y) := by
      calc y * a⁻¹ = a⁻¹ * (a * y) * a⁻¹ := by group
        _ = a⁻¹ * (ε * (y * a)) * a⁻¹ := by rw [hay]
        _ = (a⁻¹ * ε) * y := by group
        _ = ε * (a⁻¹ * y) := by rw [← hεa, mul_assoc]
    calc a⁻¹ * y = (ε * ε) * (a⁻¹ * y) := by rw [hε2, one_mul]
      _ = ε * (y * a⁻¹) := by rw [mul_assoc, ← h2]

theorem oneZ_closure {z : G} {s : Set G} (hz : z * z = 1) (hsz : ∀ x ∈ s, x * z = z * x)
    (hsq : ∀ x ∈ s, x * x = 1 ∨ x * x = z)
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x ∨ x * y = z * (y * x)) :
    (∀ x ∈ Subgroup.closure s, x * z = z * x) ∧
      (∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s,
        x * y = y * x ∨ x * y = z * (y * x)) ∧
      ∀ x ∈ Subgroup.closure s, x * x = 1 ∨ x * x = z := by
  have hzc : ∀ x ∈ Subgroup.closure s, x * z = z * x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hsz x hx
    | one => rw [one_mul, mul_one]
    | mul a b _ _ iha ihb =>
      calc a * b * z = a * (b * z) := mul_assoc a b z
        _ = a * (z * b) := by rw [ihb]
        _ = z * (a * b) := by rw [← mul_assoc, iha, mul_assoc]
    | inv a _ iha =>
      calc a⁻¹ * z = a⁻¹ * (z * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * z) * a⁻¹ := by rw [iha]
        _ = z * a⁻¹ := by group
  have toEx : ∀ {x y : G}, (x * y = y * x ∨ x * y = z * (y * x)) →
      ∃ ε, (ε = 1 ∨ ε = z) ∧ x * y = ε * (y * x) := fun {x y} h => by
    rcases h with h | h
    · exact ⟨1, Or.inl rfl, by rw [one_mul, h]⟩
    · exact ⟨z, Or.inr rfl, h⟩
  have ofEx : ∀ {x y : G}, (∃ ε, (ε = 1 ∨ ε = z) ∧ x * y = ε * (y * x)) →
      x * y = y * x ∨ x * y = z * (y * x) := fun {x y} ⟨ε, hε, h⟩ => by
    rcases hε with rfl | rfl
    · left; rw [h, one_mul]
    · right; exact h
  have hgen : ∀ y ∈ s, ∀ x ∈ Subgroup.closure s, ∃ ε, (ε = 1 ∨ ε = z) ∧ x * y = ε * (y * x) :=
    fun y hy => comm_oneZ_closure hz hzc (hsz y hy) fun x hx => toEx (hcomm x hx y hy)
  have hall : ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s,
      x * y = y * x ∨ x * y = z * (y * x) := by
    intro x hx y hy
    have hswap : ∀ g ∈ s, ∃ ε, (ε = 1 ∨ ε = z) ∧ g * x = ε * (x * g) := by
      intro g hg
      obtain ⟨ε, hε, h⟩ := hgen g hg x hx
      refine ⟨ε, hε, ?_⟩
      have hε2 : ε * ε = 1 := by
        rcases hε with rfl | rfl
        · rw [mul_one]
        · exact hz
      calc g * x = (ε * ε) * (g * x) := by rw [hε2, one_mul]
        _ = ε * (x * g) := by rw [mul_assoc, ← h]
    obtain ⟨ε, hε, h⟩ := comm_oneZ_closure hz hzc (hzc x hx) hswap y hy
    apply ofEx
    refine ⟨ε, hε, ?_⟩
    have hε2 : ε * ε = 1 := by
      rcases hε with rfl | rfl
      · rw [mul_one]
      · exact hz
    calc x * y = (ε * ε) * (x * y) := by rw [hε2, one_mul]
      _ = ε * (y * x) := by rw [mul_assoc, ← h]
  refine ⟨hzc, hall, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => left; rw [mul_one]
  | mul a b ha hb iha ihb =>
    obtain ⟨ε, hε, hba⟩ := toEx (hall b hb a ha)
    have hεa : ε * a = a * ε := oneZ_comm hε (hzc a ha)
    have h1 : a * b * (a * b) = ε * (a * a) * (b * b) := by
      calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
        _ = a * (ε * (a * b)) * b := by rw [hba]
        _ = (ε * a) * a * b * b := by rw [hεa]; simp only [mul_assoc]
        _ = ε * (a * a) * (b * b) := by simp only [mul_assoc]
    rw [h1]
    exact oneZ_mul hz (oneZ_mul hz hε iha) ihb
  | inv a _ iha =>
    have h1 : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
    rw [h1]
    exact oneZ_inv hz iha

end Central

section Tables

variable {G : Type} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem tab_mem_genTabs {gens : List G} {g : G} (hg : g ∈ gens) :
    (tab n g).toArray ∈ genTabs n gens :=
  List.mem_map_of_mem hg

theorem genTabs_cons (g : G) (gens : List G) :
    genTabs n (g :: gens) = (tab n g).toArray :: genTabs n gens := rfl

theorem genTabsInv_eq_cube {gens : List G} (h4 : ∀ g ∈ gens, g ^ 4 = 1) :
    genTabsInv n gens = (genTabs n gens).map fun e => powTab n e 3 := by
  simp only [genTabsInv, genTabs, List.map_map]
  apply List.map_congr_left
  intro g hg
  simp only [Function.comp_apply]
  rw [← CFSG.QuasithinUnique.Ch1.SporLat.tab_pow]
  congr 2
  exact (eq_inv_of_mul_eq_one_right (by rw [← pow_succ', h4 g hg])).symm

theorem mem_closure_iff_rt [Finite G] {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : G, (∀ b ∈ B, act n g b = b) → g = 1) (gens : List G) {Ts : Array (List ℕ)}
    {par cl : Array ℕ} (hEnum : BaseEnumOK n B (genTabs n gens) (genTabsInv n gens) Ts par cl)
    (x : G) : x ∈ Subgroup.closure {x | x ∈ gens} ↔
      rt n (ptsOf B (genTabs n gens)) x ∈ Ts.toList := by
  have hBP : ∀ b ∈ B, b ∈ ptsOf B (genTabs n gens) := fun b hb => List.mem_append_left _ hb
  refine ⟨benum_closed hB gens Ts par cl hEnum x, fun hx => ?_⟩
  obtain ⟨i, hi, hiT⟩ := List.getElem_of_mem hx
  have hiT' : i < Ts.size := by simpa using hi
  obtain ⟨y, hy, hyT⟩ := benum_reach hB gens Ts par cl hEnum i hiT'
  have : rt n (ptsOf B (genTabs n gens)) y = rt n (ptsOf B (genTabs n gens)) x := by
    rw [hyT, getElem!_pos Ts i hiT']
    simpa using hiT
  rwa [← rt_injective hB hBP hbase this]

theorem extraOK_spec [Finite G] {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : G, (∀ b ∈ B, act n g b = b) → g = 1) (gens : List G) (z : G)
    {Ts : Array (List ℕ)} {par cl : Array ℕ} {r : ℕ}
    (h : ExtraOK n B (genTabs n gens) (tab n z).toArray Ts par cl r) :
    Nat.card (Subgroup.closure {x | x ∈ gens}) = r ∧ z ∈ Subgroup.closure {x | x ∈ gens} ∧
      z ≠ 1 ∧ z * z = 1 ∧ (∀ x ∈ Subgroup.closure {x | x ∈ gens}, x * z = z * x) ∧
      (∀ x ∈ Subgroup.closure {x | x ∈ gens}, x * x = 1 ∨ x * x = z) ∧
      (∀ x ∈ Subgroup.closure {x | x ∈ gens}, ∀ y ∈ Subgroup.closure {x | x ∈ gens},
        x * y = y * x ∨ x * y = z * (y * x)) ∧
      ∀ x ∈ Subgroup.closure {x | x ∈ gens},
        (∀ y ∈ Subgroup.closure {x | x ∈ gens}, x * y = y * x) → x = 1 ∨ x = z := by
  obtain ⟨hEnum, hsize, hgz, hzz, hz1, hzmem, hsq, hcomm, hcen⟩ := h
  have tab1 : (tab n (1 : G)).toArray = Array.range n :=
    CFSG.QuasithinUnique.Ch1.SporLat.tab_one_toArray
  have hmem : ∀ g ∈ gens, (tab n g).toArray ∈ genTabs n gens := fun g hg =>
    List.mem_map_of_mem hg
  have hgz' : ∀ g ∈ gens, g * z = z * g := fun g hg =>
    eq_of_tabArr_eq hB hbase (by rw [tabArr_mul, tabArr_mul]; exact hgz _ (hmem g hg))
  have hz2 : z * z = 1 := eq_of_tabArr_eq hB hbase (by rw [tabArr_mul, tab1]; exact hzz)
  have hzne : z ≠ 1 := fun h1 => hz1 (by rw [h1, tab1])
  have hgsq : ∀ g ∈ gens, g * g = 1 ∨ g * g = z := by
    intro g hg
    rcases hsq _ (hmem g hg) with h1 | h1
    · left; exact eq_of_tabArr_eq hB hbase (by rw [tabArr_mul, tab1]; exact h1)
    · right; exact eq_of_tabArr_eq hB hbase (by rw [tabArr_mul]; exact h1)
  have hgcomm : ∀ g ∈ gens, ∀ g' ∈ gens, g * g' = g' * g ∨ g * g' = z * (g' * g) := by
    intro g hg g' hg'
    rcases hcomm _ (hmem g hg) _ (hmem g' hg') with h1 | h1
    · left; exact eq_of_tabArr_eq hB hbase (by rw [tabArr_mul, tabArr_mul]; exact h1)
    · right; exact eq_of_tabArr_eq hB hbase (by rw [tabArr_mul, tabArr_mul, tabArr_mul]; exact h1)
  have h4 : ∀ g ∈ gens, g ^ 4 = 1 := by
    intro g hg
    have h1 : g ^ 4 = (g * g) * (g * g) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [h1]
    rcases hgsq g hg with h2 | h2 <;> rw [h2]
    · rw [mul_one]
    · exact hz2
  rw [← genTabsInv_eq_cube h4] at hEnum
  have hP := ptsOf_lt hB gens
  have hBP : ∀ b ∈ B, b ∈ ptsOf B (genTabs n gens) := fun b hb => List.mem_append_left _ hb
  have hQmem := mem_closure_iff_rt hB hbase gens hEnum
  have hzE : z ∈ Subgroup.closure {x | x ∈ gens} :=
    (hQmem z).mpr (by rw [rt_one_mul hP]; exact hzmem)
  obtain ⟨hzc, hall, hsqall⟩ := oneZ_closure (s := {x | x ∈ gens}) hz2 hgz' hgsq hgcomm
  refine ⟨by rw [benum_card hB hbase gens Ts par cl hEnum, hsize], hzE, hzne, hz2, hzc, hsqall,
    hall, fun x hx hxc => ?_⟩
  have hxT : rt n (ptsOf B (genTabs n gens)) x ∈ Ts.toList := (hQmem x).mp hx
  have hcl := rt_comm_clause hB gens x fun s hs => hxc s (Subgroup.subset_closure hs)
  rcases hcen _ hxT hcl with h1 | h1
  · left
    exact rt_injective hB hBP hbase (by rw [h1, rt_one hP])
  · right
    exact rt_injective hB hBP hbase (by rw [h1, rt_one_mul hP])

theorem isExtraspecial2_of_extraOK [Finite G] {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : G, (∀ b ∈ B, act n g b = b) → g = 1) (gens : List G) (z : G)
    {Ts : Array (List ℕ)} {par cl : Array ℕ} {m : ℕ} (hm : 1 ≤ m)
    (h : ExtraOK n B (genTabs n gens) (tab n z).toArray Ts par cl (2 ^ (1 + 2 * m))) :
    IsExtraspecial2 m ↥(Subgroup.closure {x | x ∈ gens}) := by
  obtain ⟨hcard, hzE, hzne, -, hzc, hsq, hcomm, hcen⟩ := extraOK_spec hB hbase gens z h
  refine CFSG.Quasithin.A312ExtShapes.isExtraspecial2_of_central_involution ⟨z, hzE⟩
    (fun h1 => hzne (congrArg Subtype.val h1)) (fun y => Subtype.ext (hzc y y.2))
    (fun x => ?_) (fun x y => ?_) (fun x hx => ?_) hcard hm
  · rcases hsq x x.2 with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)
  · rcases hcomm x x.2 y y.2 with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)
  · rcases hcen x x.2 fun y hy => congrArg Subtype.val (hx ⟨y, hy⟩) with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)

end Tables

section Z4Star

variable {G : Type} [Group G]

theorem isZ4StarExtra2_of [Finite G] {V E : Subgroup G} {z4 : G} (hE : IsExtraspecial2 2 ↥E)
    (hEV : E ≤ V) (hV : Subgroup.zpowers z4 ⊔ E = V) (hz4c : ∀ x ∈ V, z4 * x = x * z4)
    (h4 : z4 ^ 4 = 1) (h2 : z4 ^ 2 ≠ 1) (h2E : z4 ^ 2 ∈ E) (h1E : z4 ∉ E) : IsZ4StarExtra2 ↥V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzV : Subgroup.zpowers z4 ≤ V := hV ▸ le_sup_left
  have hord : orderOf z4 = 4 :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) (by simpa using h4)
  refine ⟨(Subgroup.zpowers z4).subgroupOf V, E.subgroupOf V, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzV).toEquiv, Nat.card_zpowers, hord]
  · exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hzV).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hzV).symm.surjective
  · exact IsExtraspecial2.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEV).symm hE
  · intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : (x : G) ∈ Subgroup.zpowers z4 := hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx'
    apply Subtype.ext
    show (y : G) * x = x * y
    rw [← hk]
    exact ((Commute.zpow_left (hz4c y y.2) k)).symm
  · rw [← Subgroup.subgroupOf_sup hzV hEV, hV, Subgroup.subgroupOf_self]
  · have hinf : Subgroup.zpowers z4 ⊓ E = Subgroup.zpowers (z4 ^ 2) := by
      apply le_antisymm
      · rintro x ⟨hx1, hx2⟩
        have hx1 : x ∈ Subgroup.zpowers z4 := hx1
        have hx2 : x ∈ E := hx2
        rw [mem_zpowers_iff_mem_range_orderOf, hord] at hx1
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx1
        have hi4 : i < 4 := Finset.mem_range.mp hi
        interval_cases i
        · simp
        · exact absurd (by simpa using hx2) h1E
        · exact Subgroup.mem_zpowers _
        · exfalso
          apply h1E
          have h3 : z4 = (z4 ^ 3)⁻¹ := by
            apply eq_inv_of_mul_eq_one_left
            rw [← pow_succ']
            exact h4
          rw [h3]
          exact E.inv_mem hx2
      · rw [Subgroup.zpowers_le]
        exact ⟨Subgroup.npow_mem_zpowers z4 2, h2E⟩
    have h2o : orderOf (z4 ^ 2) = 2 := by
      apply orderOf_eq_prime
      · rw [← pow_mul]
        exact h4
      · exact h2
    have hle : Subgroup.zpowers z4 ⊓ E ≤ V := inf_le_left.trans hzV
    rw [show (Subgroup.zpowers z4).subgroupOf V ⊓ E.subgroupOf V =
        (Subgroup.zpowers z4 ⊓ E).subgroupOf V from (Subgroup.comap_inf _ _ _).symm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hinf, Nat.card_zpowers, h2o]

end Z4Star

section Z4Cubed

variable {G : Type} [Group G]

theorem pow_mod_four_of_pow_four {x : G} (hx : x ^ 4 = 1) (m : ℕ) : x ^ (m % 4) = x ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m 4, pow_add, pow_mul, hx, one_pow, mul_one]

theorem pow_val_add_of_pow_four {x : G} (hx : x ^ 4 = 1) (a b : ZMod 4) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, pow_mod_four_of_pow_four hx, pow_add]

@[expose] def z4Elt (w : Fin 3 → G) (c : Fin 3 → ZMod 4) : G :=
  w 0 ^ (c 0).val * w 1 ^ (c 1).val * w 2 ^ (c 2).val

theorem z4Elt_add {w : Fin 3 → G} (hc : ∀ i j, Commute (w i) (w j)) (h4 : ∀ i, w i ^ 4 = 1)
    (c d : Fin 3 → ZMod 4) : z4Elt w (c + d) = z4Elt w c * z4Elt w d := by
  unfold z4Elt
  simp only [Pi.add_apply]
  rw [pow_val_add_of_pow_four (h4 0), pow_val_add_of_pow_four (h4 1),
    pow_val_add_of_pow_four (h4 2)]
  have c01 : Commute (w 0 ^ (d 0).val) (w 1 ^ (c 1).val) := (hc 0 1).pow_pow _ _
  have c02 : Commute (w 0 ^ (d 0).val) (w 2 ^ (c 2).val) := (hc 0 2).pow_pow _ _
  have c12 : Commute (w 1 ^ (d 1).val) (w 2 ^ (c 2).val) := (hc 1 2).pow_pow _ _
  simp only [mul_assoc]
  rw [c01.left_comm, c12.left_comm, c02.left_comm]

theorem isZ4Cubed_of [Finite G] {w : Fin 3 → G} (hc : ∀ i j, Commute (w i) (w j))
    (h4 : ∀ i, w i ^ 4 = 1) (hcard : Nat.card (Subgroup.closure (Set.range w)) = 64) :
    IsZ4Cubed ↥(Subgroup.closure (Set.range w)) := by
  let f : Multiplicative (Fin 3 → ZMod 4) →* G :=
    { toFun := fun c => z4Elt w c.toAdd
      map_one' := by simp [z4Elt]
      map_mul' := fun c d => z4Elt_add hc h4 c.toAdd d.toAdd }
  have hrange : f.range = Subgroup.closure (Set.range w) := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      have hw : ∀ i, w i ∈ Subgroup.closure (Set.range w) := fun i =>
        Subgroup.subset_closure ⟨i, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (hw 0) _)
        (Subgroup.pow_mem _ (hw 1) _)) (Subgroup.pow_mem _ (hw 2) _)
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      refine ⟨Multiplicative.ofAdd (Pi.single i 1), ?_⟩
      show z4Elt w (Pi.single i 1) = w i
      have h1 : (1 : ZMod 4).val = 1 := rfl
      have h0 : (0 : ZMod 4).val = 0 := rfl
      fin_cases i <;> simp [z4Elt, h1, h0]
  have hdom : Nat.card (Multiplicative (Fin 3 → ZMod 4)) = 64 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have hsurj : Function.Surjective f.rangeRestrict := MonoidHom.rangeRestrict_surjective f
  have hbij : Function.Bijective f.rangeRestrict := by
    refine ⟨?_, hsurj⟩
    have hle : Nat.card (Multiplicative (Fin 3 → ZMod 4)) ≤ Nat.card f.range := by
      rw [hdom, hrange, hcard]
    exact (Function.Surjective.bijective_of_nat_card_le hsurj hle).1
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans (MulEquiv.ofBijective _ hbij).symm⟩

end Z4Cubed

section TablesZ4

variable {G : Type} [Group G] [Finite G] {n : ℕ} [MulAction G (Fin n)]

theorem z4StarOK_spec {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : G, (∀ b ∈ B, act n g b = b) → g = 1) (z4 : G) (gens : List G)
    {TsE : Array (List ℕ)} {parE clE : Array ℕ} {TsV : Array (List ℕ)} {parV clV : Array ℕ}
    (h : Z4StarOK n B (tab n z4).toArray (genTabs n gens) TsE parE clE TsV parV clV) :
    IsZ4StarExtra2 ↥(Subgroup.closure {x | x ∈ z4 :: gens}) ∧
      Nat.card (Subgroup.closure {x | x ∈ z4 :: gens}) = 64 := by
  obtain ⟨hE, hz44, hz4e, hz4E, hVEnum, hVsize⟩ := h
  have tab1 : (tab n (1 : G)).toArray = Array.range n :=
    CFSG.QuasithinUnique.Ch1.SporLat.tab_one_toArray
  rw [← tabArr_mul] at hE
  have hEx := isExtraspecial2_of_extraOK (m := 2) hB hbase gens (z4 * z4) (le_refl 1 |>.trans
    (by norm_num)) hE
  obtain ⟨-, hzE, hzne, -, -, hsq, -, -⟩ := extraOK_spec hB hbase gens (z4 * z4) hE
  have h4 : z4 ^ 4 = 1 := eq_of_tabArr_eq hB hbase (by
    rw [CFSG.QuasithinUnique.Ch1.SporLat.tab_pow, tab1]; exact hz44)
  have hz4g : ∀ g ∈ gens, z4 * g = g * z4 := fun g hg => eq_of_tabArr_eq hB hbase (by
    rw [tabArr_mul, tabArr_mul]; exact hz4e _ (List.mem_map_of_mem hg))
  have hg4 : ∀ g ∈ z4 :: gens, g ^ 4 = 1 := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact h4
    · have h1 : g ^ 4 = (g * g) * (g * g) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      have hzz : z4 * z4 * (z4 * z4) = 1 := by
        rw [← h4]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [h1]
      rcases hsq g (Subgroup.subset_closure hg) with h2 | h2 <;> rw [h2]
      · rw [mul_one]
      · exact hzz
  have hVgens : genTabs n (z4 :: gens) = (tab n z4).toArray :: genTabs n gens := rfl
  rw [← hVgens, ← genTabsInv_eq_cube hg4] at hVEnum
  have hcardV : Nat.card (Subgroup.closure {x | x ∈ z4 :: gens}) = 64 := by
    rw [benum_card hB hbase _ TsV parV clV hVEnum, hVsize]
  refine ⟨?_, hcardV⟩
  have hEV : Subgroup.closure {x | x ∈ gens} ≤ Subgroup.closure {x | x ∈ z4 :: gens} :=
    Subgroup.closure_mono fun x hx => List.mem_cons_of_mem _ hx
  have hV : Subgroup.zpowers z4 ⊔ Subgroup.closure {x | x ∈ gens} =
      Subgroup.closure {x | x ∈ z4 :: gens} := by
    rw [Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
    ext x
    simp [List.mem_cons]
  have hz4c : ∀ x ∈ Subgroup.closure {x | x ∈ z4 :: gens}, z4 * x = x * z4 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact hz4g x hx
    | one => rw [mul_one, one_mul]
    | mul a b _ _ iha ihb =>
      calc z4 * (a * b) = (z4 * a) * b := (mul_assoc z4 a b).symm
        _ = a * (z4 * b) := by rw [iha, mul_assoc]
        _ = a * b * z4 := by rw [ihb, mul_assoc]
    | inv a _ iha =>
      calc z4 * a⁻¹ = a⁻¹ * (a * z4) * a⁻¹ := by group
        _ = a⁻¹ * (z4 * a) * a⁻¹ := by rw [iha]
        _ = a⁻¹ * z4 := by group
  have hP := ptsOf_lt hB gens
  have hEnumE : BaseEnumOK n B (genTabs n gens) (genTabsInv n gens) TsE parE clE := by
    have hge : ∀ g ∈ gens, g ^ 4 = 1 := fun g hg => hg4 g (List.mem_cons_of_mem _ hg)
    rw [genTabsInv_eq_cube hge]
    exact hE.1
  have hz4notE : z4 ∉ Subgroup.closure {x | x ∈ gens} := fun hz =>
    hz4E (by
      have := (mem_closure_iff_rt hB hbase gens hEnumE z4).mp hz
      rwa [rt_one_mul hP] at this)
  exact isZ4StarExtra2_of hEx hEV hV hz4c h4 (by rw [pow_two]; exact hzne)
    (by rw [pow_two]; exact hzE) hz4notE

theorem z4CubedOK_spec3 {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : G, (∀ b ∈ B, act n g b = b) → g = 1) (w0 w1 w2 : G)
    {Ts : Array (List ℕ)} {par cl : Array ℕ}
    (h : Z4CubedOK n B (genTabs n [w0, w1, w2]) Ts par cl) :
    IsZ4Cubed ↥(Subgroup.closure {x | x ∈ [w0, w1, w2]}) ∧
      Nat.card (Subgroup.closure {x | x ∈ [w0, w1, w2]}) = 64 := by
  obtain ⟨-, h4t, hct, hEnum, hsize⟩ := h
  have tab1 : (tab n (1 : G)).toArray = Array.range n :=
    CFSG.QuasithinUnique.Ch1.SporLat.tab_one_toArray
  have hmem : ∀ g ∈ [w0, w1, w2], (tab n g).toArray ∈ genTabs n [w0, w1, w2] := fun g hg =>
    List.mem_map_of_mem hg
  have h4 : ∀ g ∈ [w0, w1, w2], g ^ 4 = 1 := fun g hg => eq_of_tabArr_eq hB hbase (by
    rw [CFSG.QuasithinUnique.Ch1.SporLat.tab_pow, tab1]; exact h4t _ (hmem g hg))
  have hc : ∀ g ∈ [w0, w1, w2], ∀ g' ∈ [w0, w1, w2], g * g' = g' * g := fun g hg g' hg' =>
    eq_of_tabArr_eq hB hbase (by
      rw [tabArr_mul, tabArr_mul]; exact hct _ (hmem g hg) _ (hmem g' hg'))
  rw [← genTabsInv_eq_cube h4] at hEnum
  have hcard : Nat.card (Subgroup.closure {x | x ∈ [w0, w1, w2]}) = 64 := by
    rw [benum_card hB hbase _ Ts par cl hEnum, hsize]
  let w : Fin 3 → G := ![w0, w1, w2]
  have hset : Set.range w = {x | x ∈ [w0, w1, w2]} := by
    ext x
    simp only [w, Set.mem_range, Fin.exists_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      IsEmpty.exists_iff, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      @eq_comm G x]
  have hwm : ∀ i, w i ∈ [w0, w1, w2] := fun i => by
    fin_cases i <;> simp [w]
  rw [← hset] at hcard ⊢
  exact ⟨isZ4Cubed_of (fun i j => hc _ (hwm i) _ (hwm j)) (fun i => h4 _ (hwm i)) hcard, hcard⟩

theorem z4CubedOK_spec {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : G, (∀ b ∈ B, act n g b = b) → g = 1) (gens : List G)
    {Ts : Array (List ℕ)} {par cl : Array ℕ} (h : Z4CubedOK n B (genTabs n gens) Ts par cl) :
    IsZ4Cubed ↥(Subgroup.closure {x | x ∈ gens}) ∧
      Nat.card (Subgroup.closure {x | x ∈ gens}) = 64 := by
  have hlen : gens.length = 3 := by
    rw [← genTabs_length (n := n)]
    exact h.1
  match gens, hlen, h with
  | [w0, w1, w2], _, h => exact z4CubedOK_spec3 hB hbase w0 w1 w2 h

end TablesZ4

end CFSG.Quasithin.A312S
