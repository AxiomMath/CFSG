module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymSylow
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymInputs
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolTypeInv
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolTwoLines
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolLinesH
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolNumbers

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.GH74.GLS (oResidual)

section Facts

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem sym1119_x_mem_L (h : Sec11Data G A c L a R Y d x s r g) : x ∈ L := by
  have : x ∈ R ⊓ L := by rw [h.inf_L_eq]; exact Subgroup.mem_zpowers x
  exact this.2

theorem sym1119_numbers_all (_h45 : Sec4.Item4_5) (hNum : Sym1119Numbers)
    (hL3 : Sym1119NotLThree) (hctx : Sym1119Ctx G A c L a R Y d x s r g) :
    orderOf x = 27 ∧ ∃ f ∈ Subgroup.closure ({a, c} : Set G), f ∉ Subgroup.zpowers c ∧
      r ^ 3 = f := by
  have h := hctx.big.toSec11Data
  obtain ⟨hxle, hrle⟩ :=
    hNum G A c L a R Y d x s r g hctx (hL3 G A c L a R Y d x s r g hctx)
  have hx27 : orderOf x = 27 := by
    obtain ⟨k, hk⟩ := Item1117Proof.x_pow_eq_one h
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
    have hgt := hctx.big.orderOf_x_gt
    have hj3 : 3 ≤ j := by
      by_contra hlt
      push_neg at hlt
      have : 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hj] at hgt
      omega
    have h27 : 27 ∣ orderOf x := by
      rw [hj]
      exact (pow_dvd_pow 3 hj3 : 3 ^ 3 ∣ 3 ^ j)
    exact le_antisymm hxle (Nat.le_of_dvd (orderOf_pos x) h27)
  have hrc : r * c = c * r := sym1119_R_comm_c h r (sym1119_r_mem_R h)
  have hsc : s ∈ Subgroup.zpowers c := hctx.s_eq_c ▸ Subgroup.mem_zpowers s
  have ha : a ∈ Subgroup.closure ({r, c} : Set G) := by
    refine ((Subgroup.closure_le _).mpr ?_) h.a_mem_closure
    rintro y (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hsc
  have hac : a ∉ Subgroup.zpowers c := (sym1119_indep h).1
  have hr3ne : r ^ 3 ≠ 1 := fun hr3 =>
    hctx.rs_ne (Item1119Sym.closure_eq_of_pow_three_eq_one hrc hr3 hctx.s_eq_c ha hac)
  obtain ⟨k, hk⟩ := sym1119_pow_R h (sym1119_r_mem_R h)
  obtain ⟨j, -, hordj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  have hj2 : 2 ≤ j := by
    by_contra hlt
    push_neg at hlt
    apply hr3ne
    have h3 : orderOf r ∣ 3 := by
      rw [hordj]
      exact (pow_dvd_pow 3 (by omega : j ≤ 1)).trans (by simp)
    exact orderOf_dvd_iff_pow_eq_one.mp h3
  have h9 : 9 ∣ orderOf r := by
    rw [hordj]
    exact (pow_dvd_pow 3 hj2 : 3 ^ 2 ∣ 3 ^ j)
  have hr9 : orderOf r = 9 := le_antisymm hrle (Nat.le_of_dvd (orderOf_pos r) h9)
  obtain ⟨hm1, hm2⟩ := Item1119Sym.cube_facts_of_orderOf_nine hrc
    (Item1117Proof.pow_three_of_mem_A h h.mem_A) (Item1117Proof.pow_three_of_mem_A h h.a_mem)
    hr9 ha hac
  exact ⟨hx27, r ^ 3, hm1, hm2, rfl⟩

theorem sym1119_yNotField_line (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    {e z : G} (heA : e ∈ A) (hec : e ∉ Subgroup.closure ({c, d} : Set G))
    (hz : z ∈ Subgroup.closure ({e, d} : Set G)) (hzd : z ∉ Subgroup.zpowers d) :
    YNotField c L z ↔ YNotField c L e := by
  obtain ⟨m, hm, hxa⟩ := sym1119_x_a_action h45 h
  obtain ⟨hxc, hxd⟩ := sym1119_x_comm h45 h
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h hdA
  have hd1 : d ≠ 1 := sym1119_d_ne_one h
  have hac : a * c = c * a := Item1117Proof.commute_of_mem_A h h.a_mem h.mem_A
  have had : a * d = d * a := Item1117Proof.commute_of_mem_A h h.a_mem hdA
  have hcd : c * d = d * c := Item1117Proof.commute_of_mem_A h h.mem_A hdA
  have ha3 : a ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h h.a_mem
  have hc3 : c ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h h.mem_A
  have he3 : e ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h heA
  have hed : e * d = d * e := Item1117Proof.commute_of_mem_A h heA hdA
  have hindep : a ∉ Subgroup.closure ({c, d} : Set G) := (sym1119_indep h).2.2.2.2.1
  have hxL := sym1119_x_mem_L h
  have hconj : ∀ t : ℤ, YNotField c L (d ^ t * e) ↔ YNotField c L e := by
    intro t
    obtain ⟨n, hn⟩ := Item1119Sym.x_conj_to_d_pow x a c d e m hxa hm hxc hxd hac had hcd ha3 hc3
      hd3 hd1 hindep (h.closure_eq ▸ heA) hec t
    rw [← hn]
    refine Item1119Sym.yNotField_conj c L (x ^ n) e
      (Subgroup.le_normalizer (Subgroup.zpow_mem _ hxL n)) ?_
    rw [mul_inv_eq_iff_eq_mul]
    exact (((show Commute x c from hxc).zpow_left n).eq)
  obtain ⟨j, hj | hj⟩ := Item1119Sym.mem_line_cases hed he3 hd3 hz hzd
  · rw [hj]; exact hconj j
  · rw [hj]; exact (Item1119Sym.yNotField_inv c L _).trans (hconj j)

theorem sym1119_noConjInAD (h45 : Sec4.Item4_5) (hctx : Sym1119Ctx G A c L a R Y d x s r g)
    (hK111 : Sym1119Item111) (k : G)
    (hk : k * c * k⁻¹ ∈ Subgroup.closure ({a, d} : Set G)) :
    k * c * k⁻¹ ∈ Subgroup.zpowers d := by
  by_contra hnd
  have h := hctx.big.toSec11Data
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have had : a * d = d * a := Item1117Proof.commute_of_mem_A h h.a_mem hdA
  have ha3 : a ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h h.a_mem
  have hzA : k * c * k⁻¹ ∈ A := by
    refine ((Subgroup.closure_le _).mpr ?_) hk
    rintro y (rfl | rfl)
    exacts [h.a_mem, hdA]
  have hindep : a ∉ Subgroup.closure ({c, d} : Set G) := (sym1119_indep h).2.2.2.2.1
  have hzc : k * c * k⁻¹ ∉ Subgroup.closure ({c, d} : Set G) := by
    intro hzcl
    obtain ⟨i, j, hij⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair had hk
    have hai : a ^ i ∈ Subgroup.closure ({c, d} : Set G) := by
      have e : a ^ i = (k * c * k⁻¹) * (d ^ j)⁻¹ := by rw [hij]; group
      rw [e]
      exact Subgroup.mul_mem _ hzcl (Subgroup.inv_mem _
        (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) j))
    have ha3' : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha3
    rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h0 | h1 | h2
    · apply hnd
      rw [hij, zpow_eq_zpow_emod i ha3', h0, zpow_zero, one_mul]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers d) j
    · apply hindep
      rw [zpow_eq_zpow_emod i ha3', h1, zpow_one] at hai
      exact hai
    · apply hindep
      rw [zpow_eq_zpow_emod i ha3', h2] at hai
      have : a = (a ^ (2 : ℤ))⁻¹ := by
        have h3 : a ^ (3 : ℤ) = 1 := ha3'
        calc a = a ^ (3 : ℤ) * (a ^ (2 : ℤ))⁻¹ := by group
          _ = (a ^ (2 : ℤ))⁻¹ := by rw [h3, one_mul]
      rw [this]
      exact Subgroup.inv_mem _ hai
  have hgood := hK111 G A c L a R Y d x s r g hctx _ hzA hzc ⟨k, rfl⟩
  have hyes : YNotField c L a :=
    ⟨Y, h.mem_thetaComponentsAt_Y, h.sec11K_le, hctx.big.not_field⟩
  exact hgood ((sym1119_yNotField_line h45 h h.a_mem hindep hk hnd).mpr hyes)
theorem sym1119_claimC3 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h1120 : Item1120) (hNum : Sym1119Numbers) (hL3 : Sym1119NotLThree)
    (hK111 : Sym1119Item111) (hctx : Sym1119Ctx G A c L a R Y d x s r g) :
    ∀ e ∈ A, e ∉ Subgroup.closure ({c, d} : Set G) → e ∉ Subgroup.closure ({a, d} : Set G) →
      ∃ k : G, k * c * k⁻¹ ∈ Subgroup.closure ({e, d} : Set G) ∧
        k * c * k⁻¹ ∉ Subgroup.zpowers d := by
  intro e₁ he₁A he₁c he₁a
  by_contra hviol
  push_neg at hviol
  have h := hctx.big.toSec11Data
  obtain ⟨hord, f, hf, hfc, hr3⟩ := sym1119_numbers_all h45 hNum hL3 hctx
  obtain ⟨h₀, hh₀, he₀A, he₀c⟩ := hctx.exists_h
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h hdA
  have hd1 : d ≠ 1 := sym1119_d_ne_one h
  have hac : a * c = c * a := Item1117Proof.commute_of_mem_A h h.a_mem h.mem_A
  have had : a * d = d * a := Item1117Proof.commute_of_mem_A h h.a_mem hdA
  have hcd : c * d = d * c := Item1117Proof.commute_of_mem_A h h.mem_A hdA
  have ha3 : a ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h h.a_mem
  have hc3 : c ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h h.mem_A
  have hindep : a ∉ Subgroup.closure ({c, d} : Set G) := (sym1119_indep h).2.2.2.2.1
  have hNA := hctx.N_le_A
  have hNd := hctx.N_le_d
  have hcd' : c ∉ Subgroup.zpowers d := (sym1119_indep h).2.1
  have hmemA : ∀ n ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
      n * c * n⁻¹ ∈ A := fun n hn => (Subgroup.mem_normalizer_iff.mp (hNA hn) c).mp h.mem_A
  have hnotd : ∀ n ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
      n * c * n⁻¹ ∉ Subgroup.zpowers d := fun n hn =>
    sym1119_conj_not_mem_zpowers_d h (hNd ((Subgroup.normalizer _).inv_mem hn)) hcd'
  have he₀a : h₀ * c * h₀⁻¹ ∉ Subgroup.closure ({a, d} : Set G) := fun hmem =>
    hnotd h₀ hh₀ (sym1119_noConjInAD h45 hctx hK111 h₀ hmem)
  have hclA : Subgroup.closure ({c, a, d} : Set G) = A := h.closure_eq.symm
  refine sym1119_false_of_B h45 h113 h117 h1120 hctx hord hf hfc hr3 hh₀ he₀c ?_
  intro n hn
  by_cases hz : n * c * n⁻¹ ∈ Subgroup.closure ({c, d} : Set G)
  · exact Or.inl hz
  · right
    have hza : n * c * n⁻¹ ∉ Subgroup.closure ({a, d} : Set G) := fun hmem =>
      hnotd n hn (sym1119_noConjInAD h45 hctx hK111 n hmem)
    have hne : Subgroup.closure ({h₀ * c * h₀⁻¹, d} : Set G) ≠
        Subgroup.closure ({e₁, d} : Set G) := by
      intro heq
      have hmem : h₀ * c * h₀⁻¹ ∈ Subgroup.closure ({e₁, d} : Set G) := by
        rw [← heq]; exact Subgroup.subset_closure (by simp)
      exact hnotd h₀ hh₀ (hviol h₀ hmem)
    rcases Item1119Sym.two_lines_cover a c d (h₀ * c * h₀⁻¹) e₁ (n * c * n⁻¹) hac had hcd ha3 hc3
      hd3 hd1 hindep (hclA ▸ he₀A) he₀c he₀a (hclA ▸ he₁A) he₁c he₁a (hclA ▸ hmemA n hn) hz hza
      hne with hmem | hmem
    · exact hmem
    · exact absurd (hviol n hmem) (hnotd n hn)
theorem sym1119_conj_not_mem_zpowers_d' {n u : G}
    (hn : n⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hu : u ∉ Subgroup.zpowers d) : n * u * n⁻¹ ∉ Subgroup.zpowers d := by
  intro hmem
  apply hu
  have := (Subgroup.mem_normalizer_iff.mp hn (n * u * n⁻¹)).mp hmem
  simpa [mul_assoc] using this

theorem sym1119_lines (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hctx : Sym1119Ctx G A c L a R Y d x s r g) (hK111 : Sym1119Item111)
    (hC3 : ∀ e ∈ A, e ∉ Subgroup.closure ({c, d} : Set G) →
      e ∉ Subgroup.closure ({a, d} : Set G) →
      ∃ k : G, k * c * k⁻¹ ∈ Subgroup.closure ({e, d} : Set G) ∧
        k * c * k⁻¹ ∉ Subgroup.zpowers d) :
    Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) ∧
      ∀ e ∈ A, e ∉ Subgroup.closure ({c, d} : Set G) → e ∉ Subgroup.closure ({a, d} : Set G) →
        ¬ YNotField c L e := by
  have h := hctx.big.toSec11Data
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h hdA
  have hd1 : d ≠ 1 := sym1119_d_ne_one h
  have hcd' : c ∉ Subgroup.zpowers d := (sym1119_indep h).2.1
  have hNA := hctx.N_le_A
  have hNd := hctx.N_le_d
  have hzdc : Subgroup.zpowers d ≤ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hzda : Subgroup.zpowers d ≤ Subgroup.closure ({a, d} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  constructor
  · intro n hn
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    refine Item1119Sym.conj_mem_closure_of_gens ({a, d} : Set G) (Subgroup.closure {a, d}) n ?_ hw
    rintro u (rfl | rfl)
    · by_contra hna
      have hnaA : n * u * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hNA hn) u).mp h.a_mem
      have hnad : n * u * n⁻¹ ∉ Subgroup.zpowers d :=
        sym1119_conj_not_mem_zpowers_d' (hNd ((Subgroup.normalizer _).inv_mem hn))
          (sym1119_indep h).2.2.1
      have hnac : n * u * n⁻¹ ∉ Subgroup.closure ({c, d} : Set G) := by
        intro hmem
        have h1 : (Subgroup.closure ({c, d} : Set G)).map (MulAut.conj n⁻¹).toMonoidHom =
            Subgroup.closure ({n⁻¹ * c * n⁻¹⁻¹, d} : Set G) :=
          sym1119_map_conj_line h113 h117 h (hNd ((Subgroup.normalizer _).inv_mem hn))
        have h2 : n⁻¹ * (n * u * n⁻¹) * n⁻¹⁻¹ ∈
            Subgroup.closure ({n⁻¹ * c * n⁻¹⁻¹, d} : Set G) := by
          rw [← h1]; exact ⟨_, hmem, rfl⟩
        have e1 : n⁻¹ * (n * u * n⁻¹) * n⁻¹⁻¹ = u := by group
        rw [e1] at h2
        have hnn : n⁻¹⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
          simpa using hNd hn
        have hwA : n⁻¹ * c * n⁻¹⁻¹ ∈ A :=
          (Subgroup.mem_normalizer_iff.mp (hNA ((Subgroup.normalizer _).inv_mem hn)) c).mp h.mem_A
        have hwd : n⁻¹ * c * n⁻¹⁻¹ ∉ Subgroup.zpowers d :=
          sym1119_conj_not_mem_zpowers_d' hnn hcd'
        have hline : Subgroup.closure ({u, d} : Set G) =
            Subgroup.closure ({n⁻¹ * c * n⁻¹⁻¹, d} : Set G) :=
          Item1119Sym.closure_pair_eq_of_mem (n⁻¹ * c * n⁻¹⁻¹) u d
            (Item1117Proof.commute_of_mem_A h hwA hdA) (Item1117Proof.pow_three_of_mem_A h hwA)
            hd3 hd1 hwd h2 (sym1119_indep h).2.2.1
        have hwcl : n⁻¹ * c * n⁻¹⁻¹ ∈ Subgroup.closure ({u, d} : Set G) := by
          rw [hline]; exact Subgroup.subset_closure (by simp)
        exact hwd (sym1119_noConjInAD h45 hctx hK111 n⁻¹ hwcl)
      obtain ⟨k, hk1, hk2⟩ := hC3 _ hnaA hnac hna
      have h3 : (Subgroup.closure ({u, d} : Set G)).map (MulAut.conj n).toMonoidHom =
          Subgroup.closure ({n * u * n⁻¹, d} : Set G) :=
        sym1119_map_conj_line h113 h117 h (hNd hn)
      rw [← h3] at hk1
      obtain ⟨w, hw', hwe⟩ := hk1
      have hwe' : n * w * n⁻¹ = k * c * k⁻¹ := hwe
      have hw'' : w = (n⁻¹ * k) * c * (n⁻¹ * k)⁻¹ := by
        calc w = n⁻¹ * (n * w * n⁻¹) * n := by group
          _ = n⁻¹ * (k * c * k⁻¹) * n := by rw [hwe']
          _ = (n⁻¹ * k) * c * (n⁻¹ * k)⁻¹ := by group
      have hwd := sym1119_noConjInAD h45 hctx hK111 (n⁻¹ * k) (hw'' ▸ hw')
      apply hk2
      rw [← hwe']
      exact (Subgroup.mem_normalizer_iff.mp (hNd hn) w).mp (by rw [hw'']; exact hwd)
    · exact hzda ((Subgroup.mem_normalizer_iff.mp (hNd hn) u).mp (Subgroup.mem_zpowers u))
  · intro e he hec hea
    obtain ⟨k, hkmem, hknd⟩ := hC3 e he hec hea
    have hedn : e ∉ Subgroup.zpowers d := fun hed => hec (hzdc hed)
    have hz₀A : k * c * k⁻¹ ∈ A := by
      refine ((Subgroup.closure_le _).mpr ?_) hkmem
      rintro y (rfl | rfl)
      exacts [he, hdA]
    have hz₀c : k * c * k⁻¹ ∉ Subgroup.closure ({c, d} : Set G) := by
      intro hz₀
      have hline : Subgroup.closure ({k * c * k⁻¹, d} : Set G) =
          Subgroup.closure ({e, d} : Set G) :=
        Item1119Sym.closure_pair_eq_of_mem e (k * c * k⁻¹) d
          (Item1117Proof.commute_of_mem_A h he hdA) (Item1117Proof.pow_three_of_mem_A h he) hd3 hd1
          hedn hkmem hknd
      have heq : e ∈ Subgroup.closure ({k * c * k⁻¹, d} : Set G) := by
        rw [hline]; exact Subgroup.subset_closure (by simp)
      refine hec (((Subgroup.closure_le _).mpr ?_) heq)
      rintro y (rfl | rfl)
      · exact hz₀
      · exact Subgroup.subset_closure (by simp)
    have hgood := hK111 G A c L a R Y d x s r g hctx _ hz₀A hz₀c ⟨k, rfl⟩
    have hline : Subgroup.closure ({k * c * k⁻¹, d} : Set G) =
        Subgroup.closure ({e, d} : Set G) :=
      Item1119Sym.closure_pair_eq_of_mem e (k * c * k⁻¹) d
        (Item1117Proof.commute_of_mem_A h he hdA) (Item1117Proof.pow_three_of_mem_A h he) hd3 hd1
        hedn hkmem hknd
    have heq : e ∈ Subgroup.closure ({k * c * k⁻¹, d} : Set G) := by
      rw [hline]; exact Subgroup.subset_closure (by simp)
    exact fun hy => hgood
      ((sym1119_yNotField_line h45 h hz₀A hz₀c heq hedn).mp hy)

theorem step1119Lines_holds (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h1120 : Item1120) (hNum : Sym1119Numbers) (hL3 : Sym1119NotLThree)
    (hK111 : Sym1119Item111) : Step1119Lines := by
  intro G _ _ A c L a R Y d x s r g hctx
  exact sym1119_lines h45 h113 h117 hctx hK111
    (sym1119_claimC3 h45 h113 h117 h1120 hNum hL3 hK111 hctx)

end Facts

end CFSG.RankThree.PartTwo.Sec11

end
