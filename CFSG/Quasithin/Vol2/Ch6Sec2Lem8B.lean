module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem8A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem isElemAbelian_conjSub_V (g : G) : IsElemAbelian 2 (conjSub g V) := by
  rw [conjSub_eq_conjSubgroup_ch62]
  exact isElemAbelian_conjSubgroup h.toHyp611.isElemAbelian _

theorem pair628 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5) (h6110 : Stmt6_1_10)
    (hE612 : Ch6InE612) (h627 : Stmt6_2_7) {x y : G} {W : Subgroup G}
    (hW : IsElemAbelian 2 W) (hFW : conjSub y V ≤ W)
    (hEW : conjSub x V ≤ Subgroup.normalizer (W : Set G))
    (hFE : ¬ conjSub y V ≤ Subgroup.normalizer (conjSub x V : Set G))
    (h2 : (conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)).relIndex (conjSub y V) ≤ 2) :
    ¬ conjSub x V ≤ Subgroup.normalizer (conjSub y V : Set G) ∧
    ⁅conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G), conjSub x V⁆ =
      conjSub x V ⊓ Subgroup.centralizer (conjSub y V : Set G) ∧
    Nat.card ↥(conjSub x V ⊓ Subgroup.centralizer (conjSub y V : Set G)) = 4 ∧
    (Subgroup.centralizer (conjSub x V : Set G)).relIndex
      (conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)) = 2 ∧
    Nat.card ↥(conjSub y V ⊓ Subgroup.centralizer (conjSub x V : Set G)) = 4 ∧
    (conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)).relIndex (conjSub y V) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := conjSub x V with hEdef
  set F := conjSub y V with hFdef
  set N := F ⊓ Subgroup.normalizer (E : Set G) with hNdef
  have hEel : IsElemAbelian 2 E := h.isElemAbelian_conjSub_V x
  have hFel : IsElemAbelian 2 F := h.isElemAbelian_conjSub_V y
  have hE2 : IsPGroup 2 E := B2F.isPGroup_of_isElemAbelian hEel
  have hF2 : IsPGroup 2 F := B2F.isPGroup_of_isElemAbelian hFel
  have hEc : Nat.card E = 16 := h.card_conjSub_V x
  have hFc : Nat.card F = 16 := h.card_conjSub_V y
  have hEF : ¬ E ≤ Subgroup.normalizer (F : Set G) := by
    intro hle
    apply hFE
    have h1 := h.commutator_conj_conj_eq_bot h432 h627 hle
    rw [Subgroup.commutator_comm] at h1
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1).trans
      (Subgroup.centralizer_le_normalizer _)
  have hNF : N.relIndex F = 2 := by
    have hpow := relIndex_eq_two_pow hF2 N
    have hne : N.relIndex F ≠ 1 := fun h1 => hFE (Subgroup.relIndex_eq_one.mp h1 |>.trans
      inf_le_right)
    rw [hpow] at h2 hne ⊢
    rcases Nat.lt_or_ge (mQuot F N) 2 with hlt | hge
    · interval_cases hm : mQuot F N
      · simp at hne
      · rfl
    · have : 2 ^ 2 ≤ 2 ^ mQuot F N := Nat.pow_le_pow_right (by norm_num) hge
      omega
  obtain ⟨n, hnN, hnC⟩ : ∃ n ∈ N, n ∉ Subgroup.centralizer (E : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hEF
    have hEC : E ≤ Subgroup.centralizer (N : Set G) := fun e he =>
      Subgroup.mem_centralizer_iff.mpr fun m hm =>
        (Subgroup.mem_centralizer_iff.mp (hcon m hm) e he).symm
    exact hEC.trans (h.centralizer_le_normalizer_conj h331 h432 h615 h6110 hE612 y inf_le_left
      (by rw [hNF]))
  have hcommle : ⁅N, E⁆ ≤ E ⊓ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.commutator_le]
    intro m hm e he
    rw [commutatorElement_def]
    have h1 : m * e * m⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hm.2 e).mp he
    have h3 : e * m⁻¹ * e⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hEW he) _).mp (W.inv_mem (hFW hm.1))
    have hW' : m * e * m⁻¹ * e⁻¹ ∈ W := by
      have := W.mul_mem (hFW hm.1) h3
      simpa [mul_assoc] using this
    refine ⟨E.mul_mem h1 (E.inv_mem he), Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
    exact B2F.isElemAbelian_comm hW (hFW hf) hW'
  have hnE : n ∈ Subgroup.normalizer (E : Set G) := hnN.2
  have hmemE : ∀ e ∈ E, n * e * n⁻¹ * e⁻¹ ∈ E := fun e he =>
    E.mul_mem ((Subgroup.mem_normalizer_iff.mp hnE e).mp he) (E.inv_mem he)
  let f : ↥E →* ↥E :=
    { toFun := fun e => ⟨n * e * n⁻¹ * (e : G)⁻¹, hmemE e e.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        show n * (a * b) * n⁻¹ * ((a : G) * b)⁻¹ =
          (n * a * n⁻¹ * (a : G)⁻¹) * (n * b * n⁻¹ * (b : G)⁻¹)
        have ha := (Subgroup.mem_normalizer_iff.mp hnE a).mp a.2
        have hb := (Subgroup.mem_normalizer_iff.mp hnE b).mp b.2
        have h1 := B2F.isElemAbelian_comm hEel (E.inv_mem a.2) hb
        have h1' := B2F.isElemAbelian_comm hEel (E.inv_mem a.2) (E.inv_mem b.2)
        calc n * (a * b) * n⁻¹ * ((a : G) * b)⁻¹ =
              (n * a * n⁻¹) * (n * b * n⁻¹) * ((b : G)⁻¹ * (a : G)⁻¹) := by group
          _ = (n * a * n⁻¹) * (n * b * n⁻¹) * ((a : G)⁻¹ * (b : G)⁻¹) := by rw [h1']
          _ = (n * a * n⁻¹) * ((n * b * n⁻¹) * (a : G)⁻¹) * (b : G)⁻¹ := by group
          _ = (n * a * n⁻¹) * ((a : G)⁻¹ * (n * b * n⁻¹)) * (b : G)⁻¹ := by rw [h1]
          _ = _ := by group }
  have hker : Nat.card f.ker ≤ 4 := by
    have hle : f.ker.map E.subtype ≤ E ⊓ Subgroup.centralizer ({n} : Set G) := by
      rintro _ ⟨e, he, rfl⟩
      have he1 : f e = 1 := he
      have he' : n * e * n⁻¹ * (e : G)⁻¹ = 1 := congrArg Subtype.val he1
      refine ⟨e.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      rw [Set.mem_singleton_iff.mp hw]
      have := congrArg (· * ((e : G) * n)) he'
      simp only [one_mul] at this
      show n * (e : G) = (e : G) * n
      calc n * (e : G) = n * e * n⁻¹ * (e : G)⁻¹ * ((e : G) * n) := by group
        _ = (e : G) * n := this
    calc Nat.card f.ker = Nat.card (f.ker.map E.subtype) :=
          (Subgroup.card_map_of_injective E.subtype_injective).symm
      _ ≤ Nat.card ↥(E ⊓ Subgroup.centralizer ({n} : Set G)) := Subgroup.card_le_of_le hle
      _ ≤ 4 := h.card_fix_conj_le_four h432 x hnE hnC
  have hrange : 4 ≤ Nat.card f.range := by
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hEc] at h1
    by_contra hlt
    push Not at hlt
    have : Nat.card f.ker * Nat.card f.range < 4 * 4 :=
      Nat.mul_lt_mul_of_le_of_lt hker hlt (by norm_num)
    omega
  have hcomm4 : 4 ≤ Nat.card ↥(⁅N, E⁆ : Subgroup G) := by
    have hle : f.range.map E.subtype ≤ ⁅N, E⁆ := by
      rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
      show n * e * n⁻¹ * (e : G)⁻¹ ∈ ⁅N, E⁆
      have := Subgroup.commutator_mem_commutator hnN e.2
      rwa [commutatorElement_def] at this
    calc 4 ≤ Nat.card f.range := hrange
      _ = Nat.card (f.range.map E.subtype) :=
          (Subgroup.card_map_of_injective E.subtype_injective).symm
      _ ≤ Nat.card ↥(⁅N, E⁆ : Subgroup G) := Subgroup.card_le_of_le hle
  have hUE4 : Nat.card ↥(E ⊓ Subgroup.centralizer (F : Set G)) ≤ 4 := by
    by_contra hgt
    push Not at hgt
    apply hFE
    have hFC : F ≤ Subgroup.centralizer
        ((E ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) : Set G) := fun f' hf' =>
      Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (Subgroup.mem_centralizer_iff.mp hu.2 f' hf').symm
    refine hFC.trans (h.centralizer_le_normalizer_conj h331 h432 h615 h6110 hE612 x
      inf_le_left ?_)
    have h1 := Subgroup.relIndex_mul_card (H := E ⊓ Subgroup.centralizer (F : Set G)) (K := E)
    rw [inf_of_le_left (inf_le_left.trans le_rfl : E ⊓ Subgroup.centralizer (F : Set G) ≤ E),
      hEc] at h1
    by_contra hge
    push Not at hge
    have hpow := relIndex_eq_two_pow hE2 (E ⊓ Subgroup.centralizer (F : Set G))
    have h4 : 4 ≤ (E ⊓ Subgroup.centralizer (F : Set G)).relIndex E := by
      rw [hpow] at hge ⊢
      have : 2 ≤ mQuot E (E ⊓ Subgroup.centralizer (F : Set G)) := by
        by_contra hlt
        push Not at hlt
        interval_cases hm : mQuot E (E ⊓ Subgroup.centralizer (F : Set G)) <;> simp at hge
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) this
    have : 4 * 5 ≤ (E ⊓ Subgroup.centralizer (F : Set G)).relIndex E *
        Nat.card ↥(E ⊓ Subgroup.centralizer (F : Set G)) := Nat.mul_le_mul h4 hgt
    omega
  have hUeq : ⁅N, E⁆ = E ⊓ Subgroup.centralizer (F : Set G) :=
    Subgroup.eq_of_le_of_card_ge hcommle (hUE4.trans hcomm4)
  have hU4 : Nat.card ↥(E ⊓ Subgroup.centralizer (F : Set G)) = 4 := by
    have := Subgroup.card_le_of_le hcommle
    omega
  have hmU : mQuot E (E ⊓ Subgroup.centralizer (F : Set G)) = 2 := by
    have h1 := card_eq_two_pow_mul hE2 (inf_le_left : E ⊓ Subgroup.centralizer (F : Set G) ≤ E)
    rw [hEc, hU4] at h1
    have : 2 ^ mQuot E (E ⊓ Subgroup.centralizer (F : Set G)) = 2 ^ 2 := by omega
    exact Nat.pow_right_injective le_rfl this
  have hHU : ¬ Subgroup.centralizer ((E ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) :
      Set G) ≤ Subgroup.normalizer (E : Set G) := by
    intro hle
    apply hFE
    refine le_trans (fun f' hf' => ?_) hle
    exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp hu.2 f' hf').symm
  have hNP : N ≤ Subgroup.centralizer ((E ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) :
      Set G) ⊓ Subgroup.normalizer (E : Set G) :=
    le_inf (fun m hm => Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp hu.2 m hm.1).symm) inf_le_right
  have hCN2 := h.relIndex_le_two_of_fieldType_conj h331 h432 h615 h6110 hE612 x inf_le_left hmU
    hHU hNP (hF2.to_le inf_le_left)
  have hCN : (Subgroup.centralizer (E : Set G)).relIndex N = 2 := by
    have hpow := relIndex_eq_two_pow (hF2.to_le inf_le_left : IsPGroup 2 N)
      (Subgroup.centralizer (E : Set G))
    have hne : (Subgroup.centralizer (E : Set G)).relIndex N ≠ 1 := fun h1 =>
      hnC (Subgroup.relIndex_eq_one.mp h1 hnN)
    rw [hpow] at hCN2 hne ⊢
    rcases Nat.lt_or_ge (mQuot N (Subgroup.centralizer (E : Set G))) 2 with hlt | hge
    · interval_cases hm : mQuot N (Subgroup.centralizer (E : Set G))
      · simp at hne
      · rfl
    · have : 2 ^ 2 ≤ 2 ^ mQuot N (Subgroup.centralizer (E : Set G)) :=
        Nat.pow_le_pow_right (by norm_num) hge
      omega
  have hNcard : Nat.card N = 8 := by
    have h1 := Subgroup.relIndex_mul_card (H := N) (K := F)
    rw [inf_of_le_left (inf_le_left : N ≤ F), hNF, hFc] at h1
    change 2 * Nat.card ↥N = 16 at h1
    omega
  have hUF : Nat.card ↥(F ⊓ Subgroup.centralizer (E : Set G)) = 4 := by
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (E : Set G)) (K := N)
    have e : Subgroup.centralizer (E : Set G) ⊓ N = F ⊓ Subgroup.centralizer (E : Set G) := by
      ext w
      simp only [Subgroup.mem_inf, hNdef]
      exact ⟨fun hw => ⟨hw.2.1, hw.1⟩, fun hw => ⟨hw.2, hw.1,
        Subgroup.centralizer_le_normalizer _ hw.2⟩⟩
    rw [e, hCN, hNcard] at h1
    omega
  exact ⟨hEF, hUeq, hU4, hCN, hUF, hNF⟩

end Hyp6Sec2

end CFSG.Quasithin.H13
