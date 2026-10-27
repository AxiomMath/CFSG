module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup

section Witness

variable {S : Type*} [Group S]

@[expose] def ThreeWitness (e : S) : Prop :=
  (∃ u : Fin 4 → S, Function.Injective fun i => u i * e * (u i)⁻¹) ∨
  ((∃ z : S, z * e ≠ e * z) ∧
    ((∃ x y : S, x * e = e * x ∧ y * e = e * y ∧ x * y ≠ y * x) ∨
      ∃ x : S, x * e = e * x ∧ x ^ 3 ≠ 1))

end Witness

section Main

variable {S : Type*} [Group S] [Finite S]

theorem no_index_three_elemAbelian (Zl : Finset S)
    (hW : ∀ e : S, e ∈ Zl ∨ ThreeWitness e) (E : Subgroup S)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hcube : ∀ a ∈ E, a ^ 3 = 1)
    (hidx : E.index = 3) (hcard : Zl.card < Nat.card E) : False := by
  obtain ⟨e, heE, heZ⟩ : ∃ e ∈ E, e ∉ Zl := by
    by_contra h
    have h : ∀ e ∈ E, e ∈ Zl := fun e he => by_contra fun hn => h ⟨e, he, hn⟩
    have hsub : (E : Set S) ⊆ (Zl : Set S) := fun e he => h e he
    have h1 : (E : Set S).ncard ≤ (Zl : Set S).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet Zl)
    rw [Set.ncard_coe_finset] at h1
    have h2 : (E : Set S).ncard = Nat.card E := by
      rw [← Nat.card_coe_set_eq]
      rfl
    omega
  rcases hW e with hZ | hA | ⟨⟨z, hz⟩, hBC⟩
  · exact heZ hZ
  ·
    obtain ⟨u, hu⟩ := hA
    have : Finite (S ⧸ E) := inferInstance
    have := Fintype.ofFinite (S ⧸ E)
    have hlt : Fintype.card (S ⧸ E) < Fintype.card (Fin 4) := by
      rw [← Nat.card_eq_fintype_card, Fintype.card_fin]
      change E.index < 4
      omega
    obtain ⟨i, j, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin 4 => (u k : S ⧸ E)) hlt
    have hw : (u i)⁻¹ * u j ∈ E := QuotientGroup.eq.1 hf
    have hc := hcomm _ hw e heE
    apply hij
    apply hu
    show u i * e * (u i)⁻¹ = u j * e * (u j)⁻¹
    have hj : u j = u i * ((u i)⁻¹ * u j) := by group
    calc u i * e * (u i)⁻¹
        = u i * (e * ((u i)⁻¹ * u j) * ((u i)⁻¹ * u j)⁻¹) * (u i)⁻¹ := by
          rw [mul_assoc e, mul_inv_cancel, mul_one]
      _ = u i * (((u i)⁻¹ * u j) * e * ((u i)⁻¹ * u j)⁻¹) * (u i)⁻¹ := by rw [← hc]
      _ = u j * e * (u j)⁻¹ := by group
  ·
    have hEC : E ≤ Subgroup.centralizer {e} := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm a ha e heE
    have hCtop : Subgroup.centralizer {e} ≠ ⊤ := by
      intro h
      have hzC : z ∈ Subgroup.centralizer ({e} : Set S) := by rw [h]; exact Subgroup.mem_top z
      exact hz (Subgroup.mem_centralizer_singleton_iff.1 hzC)
    have hrel := Subgroup.relIndex_mul_index hEC
    rw [hidx] at hrel
    have hdvd : (Subgroup.centralizer ({e} : Set S)).index ∣ 3 :=
      ⟨_, hrel.symm.trans (mul_comm _ _)⟩
    have hC1 : (Subgroup.centralizer ({e} : Set S)).index ≠ 1 := fun h =>
      hCtop (Subgroup.index_eq_one.1 h)
    have hC3 : (Subgroup.centralizer ({e} : Set S)).index = 3 :=
      ((Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd).resolve_left hC1)
    have hrel1 : E.relIndex (Subgroup.centralizer ({e} : Set S)) = 1 := by
      rw [hC3] at hrel
      omega
    have hCE : Subgroup.centralizer ({e} : Set S) ≤ E := Subgroup.relIndex_eq_one.1 hrel1
    have hmem : ∀ x : S, x * e = e * x → x ∈ E := fun x hx =>
      hCE (Subgroup.mem_centralizer_singleton_iff.2 hx)
    rcases hBC with ⟨x, y, hx, hy, hxy⟩ | ⟨x, hx, hx3⟩
    · exact hxy (hcomm x (hmem x hx) y (hmem y hy))
    · exact hx3 (hcube x (hmem x hx))

end Main

section Closure

variable {G : Type*} [Group G] [Finite G]

theorem mem_of_closure_of_right_closed {gens L : Set G} (h1 : (1 : G) ∈ L)
    (hL : ∀ x ∈ L, ∀ g ∈ gens, x * g ∈ L) : ∀ y ∈ Subgroup.closure gens, y ∈ L := by
  have key : ∀ y ∈ Subgroup.closure gens, ∀ x ∈ L, x * y ∈ L := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem g hg => exact fun x hx => hL x hx g hg
    | one => exact fun x hx => by simpa using hx
    | mul a b _ _ iha ihb =>
      intro x hx
      rw [← mul_assoc]
      exact ihb _ (iha x hx)
    | inv a _ iha =>
      have hpow : ∀ n : ℕ, ∀ x ∈ L, x * a ^ n ∈ L := by
        intro n
        induction n with
        | zero => exact fun x hx => by simpa using hx
        | succ n ihn =>
          intro x hx
          rw [pow_succ, ← mul_assoc]
          exact iha _ (ihn x hx)
      have hord : a⁻¹ = a ^ (orderOf a - 1) := by
        have hpos := orderOf_pos a
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
      intro x hx
      rw [hord]
      exact hpow _ x hx
  intro y hy
  simpa using key y hy 1 h1

end Closure

section Sylow

variable {T : Type*} [Group T] [Finite T]

theorem exists_conj_le_of_sylow {p k : ℕ} [hp : Fact p.Prime] (S : Subgroup T)
    (hS : Nat.card S = p ^ k) (hT : ¬ p ^ (k + 1) ∣ Nat.card T) (D : Subgroup T)
    (hD : IsPGroup p D) : ∃ g : T, D.map (MulAut.conj g).toMonoidHom ≤ S := by
  have hidx : ¬ p ∣ S.index := by
    intro hd
    apply hT
    have h := S.card_mul_index
    rw [hS] at h
    rw [← h]
    obtain ⟨m, hm⟩ := hd
    rw [hm]
    exact ⟨m, by ring⟩
  have hSp : IsPGroup p S := IsPGroup.of_card hS
  obtain ⟨P, hDP⟩ := hD.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq T P (hSp.toSylow hidx)
  refine ⟨g, ?_⟩
  have h1 : (g • P : Sylow p T) = hSp.toSylow hidx := hg
  have h2 := congrArg (fun Q : Sylow p T => (Q : Subgroup T)) h1
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h2
  rw [← h2, Subgroup.pointwise_smul_def]
  exact Subgroup.map_mono hDP

end Sylow

section Interface

variable {T : Type*} [Group T] [Finite T]

theorem no_elemAbelian_five_of_sylow (S : Subgroup T) (hS : Nat.card S = 3 ^ 6)
    (hT : ¬ 3 ^ 7 ∣ Nat.card T) (Zl : Finset S) (hZl : Zl.card < 3 ^ 5)
    (hW : ∀ e : S, e ∈ Zl ∨ ThreeWitness e) (D : Subgroup T)
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hcube : ∀ a ∈ D, a ^ 3 = 1)
    (hcard : Nat.card D = 3 ^ 5) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDp : IsPGroup 3 D := IsPGroup.of_card hcard
  obtain ⟨g, hg⟩ := exists_conj_le_of_sylow (p := 3) (k := 6) S hS hT D hDp
  set D' := D.map (MulAut.conj g).toMonoidHom with hD'
  have hD'card : Nat.card D' = 3 ^ 5 := by
    rw [hD', Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  let E : Subgroup S := D'.subgroupOf S
  have hEcard : Nat.card E = 3 ^ 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hg).toEquiv]
    exact hD'card
  have hEidx : E.index = 3 := by
    have h := E.card_mul_index
    rw [hEcard, hS] at h
    have : 3 ^ 5 * E.index = 3 ^ 5 * 3 := by rw [h]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hmem : ∀ a ∈ E, ∃ a₀ ∈ D, (MulAut.conj g) a₀ = (a : T) := by
    intro a ha
    obtain ⟨a₀, ha₀, ha₁⟩ := Subgroup.mem_map.1 (show (a : T) ∈ D' from ha)
    exact ⟨a₀, ha₀, ha₁⟩
  have hcomm' : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a₀, ha₀, ha₁⟩ := hmem a ha
    obtain ⟨b₀, hb₀, hb₁⟩ := hmem b hb
    apply Subtype.ext
    show (a : T) * b = (b : T) * a
    rw [← ha₁, ← hb₁, ← map_mul, ← map_mul, hcomm a₀ ha₀ b₀ hb₀]
  have hcube' : ∀ a ∈ E, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨a₀, ha₀, ha₁⟩ := hmem a ha
    apply Subtype.ext
    show (a : T) ^ 3 = 1
    rw [← ha₁, ← map_pow, hcube a₀ ha₀, map_one]
  exact no_index_three_elemAbelian Zl hW E hcomm' hcube' hEidx (by rw [hEcard]; exact hZl)

theorem no_elemAbelian_five_of_sylow_isElementaryAbelian (S : Subgroup T)
    (hS : Nat.card S = 3 ^ 6) (hT : ¬ 3 ^ 7 ∣ Nat.card T) (Zl : Finset S)
    (hZl : Zl.card < 3 ^ 5) (hW : ∀ e : S, e ∈ Zl ∨ ThreeWitness e) (D : Subgroup T)
    (hD : CFSG.IsElementaryAbelian 3 D) (hcard : Nat.card D = 3 ^ 5) : False :=
  no_elemAbelian_five_of_sylow S hS hT Zl hZl hW D
    (fun a ha b hb => congrArg Subtype.val
      (hD.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    (fun a ha => CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) a ha) hcard

end Interface


section Table

variable {G : Type*} [Group G]

theorem fin4_injective {α : Type*} {f : Fin 4 → α} (h01 : f 0 ≠ f 1) (h02 : f 0 ≠ f 2)
    (h03 : f 0 ≠ f 3) (h12 : f 1 ≠ f 2) (h13 : f 1 ≠ f 3) (h23 : f 2 ≠ f 3) :
    Function.Injective f := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp_all [eq_comm])

@[expose] def TableWitness (sel : ℕ → G) (i : ℕ) : Prop :=
  (∃ u : Fin 4 → ℕ, (∀ k, u k < 729) ∧
      Function.Injective fun k => sel (u k) * sel i * (sel (u k))⁻¹) ∨
  ((∃ z < 729, sel z * sel i ≠ sel i * sel z) ∧
    ((∃ x y : ℕ, x < 729 ∧ y < 729 ∧ sel x * sel i = sel i * sel x ∧
        sel y * sel i = sel i * sel y ∧ sel x * sel y ≠ sel y * sel x) ∨
      ∃ x < 729, sel x * sel i = sel i * sel x ∧ sel x ^ 3 ≠ 1))

variable [Finite G]

theorem no_elemAbelian_five_of_table {ι : Type*} (gens : ι → G) (sel : ℕ → G)
    (hone : sel 0 = 1) (hinj : ∀ i < 729, ∀ j < 729, sel i = sel j → i = j)
    (hmem : ∀ i < 729, sel i ∈ Subgroup.closure (Set.range gens))
    (hrt : ∀ i < 729, ∀ k, ∃ j < 729, sel i * gens k = sel j)
    (zl : Finset ℕ) (hzl : zl.card < 3 ^ 5) (hW : ∀ i < 729, i ∈ zl ∨ TableWitness sel i)
    (hG : ¬ 3 ^ 7 ∣ Nat.card G) (D : Subgroup G)
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hcube : ∀ a ∈ D, a ^ 3 = 1)
    (hcard : Nat.card D = 3 ^ 5) : False := by
  classical
  set S : Subgroup G := Subgroup.closure (Set.range gens) with hSdef
  have hexists : ∀ y ∈ S, ∃ i < 729, y = sel i := by
    intro y hy
    exact mem_of_closure_of_right_closed (gens := Set.range gens)
      (L := {x | ∃ i < 729, x = sel i}) ⟨0, by norm_num, hone.symm⟩
      (by
        rintro x ⟨i, hi, rfl⟩ g ⟨k, rfl⟩
        obtain ⟨j, hj, hij⟩ := hrt i hi k
        exact ⟨j, hj, hij⟩) y hy
  have hS : Nat.card S = 3 ^ 6 := by
    have hset : (S : Set G) = Set.range (fun i : Fin 729 => sel i) := by
      ext y
      constructor
      · intro hy
        obtain ⟨i, hi, rfl⟩ := hexists y hy
        exact ⟨⟨i, hi⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact hmem i i.2
    have hinj' : Function.Injective (fun i : Fin 729 => sel i) :=
      fun a b h => Fin.ext (hinj a a.2 b b.2 h)
    calc Nat.card S = Nat.card (S : Set G) := rfl
      _ = Nat.card (Set.range (fun i : Fin 729 => sel i)) := by rw [hset]
      _ = Nat.card (Fin 729) := Nat.card_range_of_injective hinj'
      _ = 3 ^ 6 := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  let sS : ℕ → S := fun i => if h : i < 729 then ⟨sel i, hmem i h⟩ else 1
  have hcoe : ∀ {j : ℕ}, j < 729 → ((sS j : S) : G) = sel j := fun {j} hj => by simp [sS, hj]
  refine no_elemAbelian_five_of_sylow S hS hG (zl.image sS)
    (lt_of_le_of_lt Finset.card_image_le hzl) ?_ D hcomm hcube hcard
  intro e
  obtain ⟨i, hi, hei⟩ := hexists e e.2
  have he : (e : G) = sel i := hei
  rcases hW i hi with hz | hw
  · exact Or.inl (Finset.mem_image.2 ⟨i, hz, Subtype.ext (by rw [hcoe hi, he])⟩)
  · right
    rcases hw with ⟨u, hu, hinjc⟩ | ⟨⟨z, hz, hzne⟩, hBC⟩
    · refine Or.inl ⟨fun k => sS (u k), ?_⟩
      intro k l hkl
      apply hinjc
      have := congrArg Subtype.val hkl
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, hcoe (hu k), hcoe (hu l), he] using this
    · refine Or.inr ⟨⟨sS z, fun h => hzne ?_⟩, ?_⟩
      · have := congrArg Subtype.val h
        simpa [Subgroup.coe_mul, hcoe hz, he] using this
      · rcases hBC with ⟨x, y, hx, hy, hxc, hyc, hxy⟩ | ⟨x, hx, hxc, hx3⟩
        · refine Or.inl ⟨sS x, sS y, ?_, ?_, fun h => hxy ?_⟩
          · apply Subtype.ext
            simpa [Subgroup.coe_mul, hcoe hx, he] using hxc
          · apply Subtype.ext
            simpa [Subgroup.coe_mul, hcoe hy, he] using hyc
          · have := congrArg Subtype.val h
            simpa [Subgroup.coe_mul, hcoe hx, hcoe hy] using this
        · refine Or.inr ⟨sS x, ?_, fun h => hx3 ?_⟩
          · apply Subtype.ext
            simpa [Subgroup.coe_mul, hcoe hx, he] using hxc
          · have := congrArg Subtype.val h
            simpa [Subgroup.coe_pow, hcoe hx] using this

end Table

end CFSG.RankThree.PartOne.F106
