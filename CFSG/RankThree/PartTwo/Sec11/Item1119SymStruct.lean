module

public import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofBasic
public import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolActTrivial
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolYR
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolCommuteATriple
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolSmallPure1
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolMForm
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolFixR
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolCommW0

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.GH74.GLS (oResidual)

section Facts

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem sym1119_x_mem_R (h : Sec11Data G A c L a R Y d x s r g) : x ∈ R := by
  rw [h.R_eq]; exact Subgroup.subset_closure (by simp)

theorem sym1119_r_mem_R (h : Sec11Data G A c L a R Y d x s r g) : r ∈ R := by
  rw [h.R_eq]; exact Subgroup.subset_closure (by simp)

theorem sym1119_s_mem_R (h : Sec11Data G A c L a R Y d x s r g) : s ∈ R := by
  rw [h.R_eq]; exact Subgroup.subset_closure (by simp)

theorem sym1119_pow_R (h : Sec11Data G A c L a R Y d x s r g) {u : G} (hu : u ∈ R) :
    ∃ k : ℕ, u ^ 3 ^ k = 1 := Item1116Proof.exists_pow_eq_one_of_mem h hu

theorem sym1119_R_comm_c (h : Sec11Data G A c L a R Y d x s r g) :
    ∀ u ∈ R, u * c = c * u :=
  fun u hu => Subgroup.mem_centralizer_singleton_iff.mp (Item1119Proof.R_le_centralizer_c h hu)

theorem sym1119_g_comm_a (h : Sec11Data G A c L a R Y d x s r g) : g * a = a * g := by
  have hg : g ∈ Y := (h.g_mem).1
  have hYC := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y hg
  exact Subgroup.mem_centralizer_singleton_iff.mp hYC

theorem sym1119_x_a_action (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) :
    ∃ m : ℤ, ¬ (3 : ℤ) ∣ m ∧ x * a * x⁻¹ = d ^ m * a := by
  obtain ⟨hmem, hne⟩ := Item1119Proof.commutator_x_a_facts h45 h
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h (Item1117Proof.d_mem_A h)
  refine ⟨m, fun h3 => hne ?_, ?_⟩
  · rw [← hm]
    obtain ⟨k, hk⟩ := h3
    rw [hk, zpow_mul]
    have : d ^ (3 : ℤ) = 1 := by exact_mod_cast hd3
    rw [this, one_zpow]
  · have e : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
    rw [e, ← hm]

theorem sym1119_x_comm (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) :
    x * c = c * x ∧ x * d = d * x := by
  refine ⟨sym1119_R_comm_c h x (sym1119_x_mem_R h), ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Item1115Proof.d_mem_zpowers_x h)
  rw [← hk]
  exact ((Commute.refl x).zpow_right k).eq
theorem sym1119_indep (h : Sec11Data G A c L a R Y d x s r g) :
    a ∉ Subgroup.zpowers c ∧ c ∉ Subgroup.zpowers d ∧ a ∉ Subgroup.zpowers d ∧
    (∀ z ∈ Subgroup.closure ({a, c} : Set G), z ∈ Subgroup.zpowers d → z = 1) ∧
    a ∉ Subgroup.closure ({c, d} : Set G) ∧ c ∉ Subgroup.closure ({a, d} : Set G) ∧
    d ∉ Subgroup.closure ({a, c} : Set G) := by
  have hcard : Nat.card (Subgroup.closure ({c, a, d} : Set G)) = 27 := by
    rw [← h.closure_eq]; exact h.card_eq
  exact Item1119Sym.independence_of_card a c d
    (Item1117Proof.commute_of_mem_A h h.a_mem h.mem_A)
    (Item1117Proof.commute_of_mem_A h h.a_mem (Item1117Proof.d_mem_A h))
    (Item1117Proof.commute_of_mem_A h h.mem_A (Item1117Proof.d_mem_A h))
    (Item1117Proof.pow_three_of_mem_A h h.a_mem) (Item1117Proof.pow_three_of_mem_A h h.mem_A)
    (Item1117Proof.pow_three_of_mem_A h (Item1117Proof.d_mem_A h)) hcard

theorem sym1119_d_ne_one (h : Sec11Data G A c L a R Y d x s r g) : d ≠ 1 := by
  intro h1
  have := Item1117Proof.orderOf_d h
  rw [h1] at this
  simp at this

theorem sym1119_g_c_action (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) :
    ∃ κ : ℤ, ¬ (3 : ℤ) ∣ κ ∧ g * c * g⁻¹ = d ^ κ * c := by
  obtain ⟨-, hcd', -⟩ := sym1119_indep h
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h (Item1117Proof.d_mem_A h)
  have hc3 : c ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h h.mem_A
  have hcd : c * d = d * c := Item1117Proof.commute_of_mem_A h h.mem_A (Item1117Proof.d_mem_A h)
  have hgd : g * d = d * g :=
    Item1119Proof.commute_of_mem_zpowers_d h113 h117 h (Subgroup.mem_zpowers d)
      (Item1119Proof.g_mem_P R g)
  have hgd' : g * d * g⁻¹ ∈ Subgroup.zpowers d := by
    rw [hgd]; simpa using Subgroup.mem_zpowers d
  obtain ⟨j, hj⟩ := Item1119Sym.conj_eq_of_three_power_order g c d h.pow_eq_one hc3 hcd hcd' hgd'
    h.conj_mem
  refine ⟨j, fun h3 => h.g_not_mem ?_, ?_⟩
  · have hdj : d ^ j = 1 := by
      obtain ⟨k, hk⟩ := h3
      rw [hk, zpow_mul]
      have : d ^ (3 : ℤ) = 1 := by exact_mod_cast hd3
      rw [this, one_zpow]
    rw [hdj, mul_one] at hj
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    rw [← conj_zpow, hj]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k
  · rw [hj]
    exact (show Commute c (d ^ j) from (show Commute c d from hcd).zpow_right j).eq
theorem sym1119_closure_ac_le_A (h : Sec11Data G A c L a R Y d x s r g) :
    Subgroup.closure ({a, c} : Set G) ≤ A := by
  rw [Subgroup.closure_le]
  rintro y (rfl | rfl)
  exacts [h.a_mem, h.mem_A]

@[expose] def sym1119M (A : Subgroup G) (x r : G) : Subgroup G :=
  Subgroup.closure ((A : Set G) ∪ {x ^ 3, r})

@[expose] def sym1119W0 (A : Subgroup G) (x : G) : Subgroup G :=
  Subgroup.closure ((A : Set G) ∪ {x ^ 3})

theorem sym1119_A_comm_y (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) :
    ∀ u ∈ A, u * x ^ 3 = x ^ 3 * u := by
  intro u hu
  have hle : A ≤ Subgroup.centralizer ({x ^ 3} : Set G) := by
    rw [h.closure_eq, Subgroup.closure_le]
    intro v hv
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨hxc, hxd⟩ := sym1119_x_comm h45 h
    rcases hv with rfl | rfl | rfl
    · exact (((show Commute x v from hxc).pow_left 3).eq).symm
    · have := (Item1119Proof.a_x_facts h45 h).1
      exact mul_inv_eq_iff_eq_mul.mp this
    · exact (((show Commute x v from hxd).pow_left 3).eq).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hu)

theorem sym1119_A_comm_r (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hra : r * a = a * r) :
    ∀ u ∈ A, u * r = r * u := by
  intro u hu
  have hle : A ≤ Subgroup.centralizer ({r} : Set G) := by
    rw [h.closure_eq, Subgroup.closure_le]
    intro v hv
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hv with rfl | rfl | rfl
    · exact (sym1119_R_comm_c h r (sym1119_r_mem_R h)).symm
    · exact hra.symm
    · exact (Item1119Proof.commute_of_mem_zpowers_d h113 h117 h (Subgroup.mem_zpowers v)
        (Item1119Proof.R_le_P R g (sym1119_r_mem_R h))).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hu)
theorem sym1119_A_le_M (A : Subgroup G) (x r : G) : A ≤ sym1119M A x r := fun u hu =>
  Subgroup.subset_closure (Or.inl hu)

theorem sym1119_y_mem_M (A : Subgroup G) (x r : G) : x ^ 3 ∈ sym1119M A x r :=
  Subgroup.subset_closure (Or.inr (by simp))

theorem sym1119_r_mem_M (A : Subgroup G) (x r : G) : r ∈ sym1119M A x r :=
  Subgroup.subset_closure (Or.inr (by simp))

theorem sym1119_CP_A_le (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hra : r * a = a * r) (hg3 : g ^ 3 = 1)
    (hs : Subgroup.zpowers s = Subgroup.zpowers c) :
    sec11P R g ⊓ Subgroup.centralizer (A : Set G) ≤ sym1119M A x r := by
  intro z hz
  obtain ⟨hzP, hzC⟩ := hz
  obtain ⟨κ, hκ, hgc⟩ := sym1119_g_c_action h113 h117 h
  obtain ⟨m, hm, hxa⟩ := sym1119_x_a_action h45 h
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h (Item1117Proof.d_mem_A h)
  have hd1 : d ≠ 1 := sym1119_d_ne_one h
  have hcd : c * d = d * c := Item1117Proof.commute_of_mem_A h h.mem_A (Item1117Proof.d_mem_A h)
  have had : a * d = d * a := Item1117Proof.commute_of_mem_A h h.a_mem (Item1117Proof.d_mem_A h)
  have hgd : g * d = d * g :=
    Item1119Proof.commute_of_mem_zpowers_d h113 h117 h (Subgroup.mem_zpowers d)
      (Item1119Proof.g_mem_P R g)
  have hord : orderOf d = 3 := Item1117Proof.orderOf_d h
  obtain ⟨u, huR, j, rfl⟩ := Item1119Sym.mem_sup_zpowers_form R g h.g_mem_normalizer hzP
  have hzc : c * (u * g ^ j) = (u * g ^ j) * c := Subgroup.mem_centralizer_iff.mp hzC c h.mem_A
  have huc : u * c = c * u := sym1119_R_comm_c h u huR
  have h1 : u * (c * g ^ j) = u * (g ^ j * c) := by
    calc u * (c * g ^ j) = (u * c) * g ^ j := by rw [mul_assoc]
      _ = (c * u) * g ^ j := by rw [huc]
      _ = c * (u * g ^ j) := by rw [mul_assoc]
      _ = (u * g ^ j) * c := hzc
      _ = u * (g ^ j * c) := by rw [mul_assoc]
  have hgj : c * g ^ j = g ^ j * c := mul_left_cancel h1
  have hconj := Item1119Sym.zpow_conj_of_comm g c d κ hgc hgd hcd j
  have hdj : d ^ (j * κ) = 1 := by
    have e1 : g ^ j * c * (g ^ j)⁻¹ = c := by rw [← hgj]; group
    have e2 : d ^ (j * κ) * c = c := by rw [← hconj, e1]
    simpa using e2
  have h3 : (3 : ℤ) ∣ j * κ := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := d) (i := j * κ)).mpr hdj
    rw [hord] at this
    exact_mod_cast this
  have h3j : (3 : ℤ) ∣ j := by
    rcases Int.prime_three.dvd_or_dvd h3 with h3' | h3'
    · exact h3'
    · exact absurd h3' hκ
  have hgj1 : g ^ j = 1 := by
    obtain ⟨k, hk⟩ := h3j
    rw [hk, zpow_mul]
    have : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg3
    rw [this, one_zpow]
  rw [hgj1, mul_one] at hzC ⊢
  have hsc : s ∈ Subgroup.zpowers c := hs ▸ Subgroup.mem_zpowers s
  have hRle : R ≤ Subgroup.closure ({r, x, c} : Set G) := by
    rw [h.R_eq]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hsc
  have hrR : r ∈ R := sym1119_r_mem_R h
  have hux : r * x * r⁻¹ ∈ Subgroup.zpowers x :=
    (Subgroup.mem_normalizer_iff.mp (Item1115Proof.mem_normalizer_zpowers_x h45 h hrR) x).mp
      (Subgroup.mem_zpowers x)
  have hux' : r⁻¹ * x * r ∈ Subgroup.zpowers x := by
    have := (Subgroup.mem_normalizer_iff.mp
      (Item1115Proof.mem_normalizer_zpowers_x h45 h (R.inv_mem hrR)) x).mp (Subgroup.mem_zpowers x)
    simpa using this
  obtain ⟨j', i, l, hu⟩ := Item1119Sym.commute_a_triple_form r x c a d m
    (sym1119_R_comm_c h r hrR).symm (sym1119_x_comm h45 h).1.symm
    (Item1117Proof.commute_of_mem_A h h.mem_A h.a_mem) hux hux' hra hxa (sym1119_x_comm h45 h).2
    had hd3 hd1 hm (hRle huR) (Subgroup.mem_centralizer_iff.mp hzC a h.a_mem).symm
  rw [hu]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.zpow_mem _ (sym1119_r_mem_M A x r) _)
    (Subgroup.zpow_mem _ (sym1119_y_mem_M A x r) _))
    (Subgroup.zpow_mem _ (sym1119_A_le_M A x r h.mem_A) _)
theorem sym1119_yr_facts (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hord : orderOf x = 27)
    {f : G} (hf : f ∈ Subgroup.closure ({a, c} : Set G)) (hfc : f ∉ Subgroup.zpowers c)
    (hr3 : r ^ 3 = f) :
    r * x * r⁻¹ * x⁻¹ ∈ Subgroup.zpowers (x ^ 3) ∧
    x ^ 3 * r * (x ^ 3)⁻¹ * r⁻¹ ∈ Subgroup.zpowers d ∧ x ^ 3 * r * (x ^ 3)⁻¹ * r⁻¹ ≠ 1 := by
  have hx27 : x ^ 27 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hord] at this
  have hx9 : x ^ 9 ≠ 1 := by
    intro h9
    have := orderOf_dvd_of_pow_eq_one h9
    rw [hord] at this
    norm_num at this
  have hrR := sym1119_r_mem_R h
  have hrx : r * x * r⁻¹ ∈ Subgroup.zpowers x :=
    (Subgroup.mem_normalizer_iff.mp (Item1115Proof.mem_normalizer_zpowers_x h45 h hrR) x).mp
      (Subgroup.mem_zpowers x)
  have hzd : Subgroup.zpowers d = Subgroup.zpowers (x ^ 9) :=
    Item1119Sym.zpowers_eq_of_orderOf x d hord (Item1115Proof.d_mem_zpowers_x h)
      (Item1117Proof.orderOf_d h)
  have hrd : r * d = d * r :=
    Item1119Proof.commute_of_mem_zpowers_d h113 h117 h (Subgroup.mem_zpowers d)
      (Item1119Proof.R_le_P R g hrR)
  have hr9 : r * x ^ 9 = x ^ 9 * r := by
    have hx9d : x ^ 9 ∈ Subgroup.zpowers d := hzd ▸ Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx9d
    rw [← hk]
    exact ((show Commute r d from hrd).zpow_right k).eq
  obtain ⟨m, hm, hxa⟩ := sym1119_x_a_action h45 h
  obtain ⟨hxc, hxd⟩ := sym1119_x_comm h45 h
  have hac : a * c = c * a := Item1117Proof.commute_of_mem_A h h.a_mem h.mem_A
  have had : a * d = d * a := Item1117Proof.commute_of_mem_A h h.a_mem (Item1117Proof.d_mem_A h)
  have hcd : c * d = d * c := Item1117Proof.commute_of_mem_A h h.mem_A (Item1117Proof.d_mem_A h)
  have ha3 : a ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h h.a_mem
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h (Item1117Proof.d_mem_A h)
  obtain ⟨i, j, hij⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hac hf
  have hi : ¬ (3 : ℤ) ∣ i := by
    rintro ⟨k, rfl⟩
    apply hfc
    rw [hij, zpow_mul]
    have : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha3
    rw [this, one_zpow, one_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) j
  have hfx : f * x ≠ x * f :=
    Item1119Sym.not_commute_of_mem_closure_pair a c d x f i j m hij hi hxa hm hxc hxd had hcd hac
      hd3 (sym1119_d_ne_one h)
  obtain ⟨h1, h2, h3⟩ := Item1119Sym.comm_pow3_of_normalizes x r f hx27 hx9
    (sym1119_pow_R h hrR) hrx hr9 hr3 hfx
  refine ⟨h1, ?_, ?_⟩
  · have e : x ^ 3 * r * (x ^ 3)⁻¹ * r⁻¹ = (r * x ^ 3 * r⁻¹ * (x ^ 3)⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ (hzd ▸ h2)
  · intro h1'
    apply h3
    have e : r * x ^ 3 * r⁻¹ * (x ^ 3)⁻¹ = (x ^ 3 * r * (x ^ 3)⁻¹ * r⁻¹)⁻¹ := by group
    rw [e, h1', inv_one]
theorem sym1119_conj_comm {u y n : G} (hu : (n⁻¹ * u * n) * y = y * (n⁻¹ * u * n)) :
    u * (n * y * n⁻¹) = (n * y * n⁻¹) * u := by
  calc u * (n * y * n⁻¹) = n * ((n⁻¹ * u * n) * y) * n⁻¹ := by group
    _ = n * (y * (n⁻¹ * u * n)) * n⁻¹ := by rw [hu]
    _ = (n * y * n⁻¹) * u := by group

theorem sym1119_mem_W0_iff (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) {z : G} :
    z ∈ sym1119W0 A x ↔ ∃ (i : ℤ) (u : G), u ∈ A ∧ z = (x ^ 3) ^ i * u :=
  Item1119Sym.mem_closure_union_zpowers_form A (x ^ 3) (sym1119_A_comm_y h45 h)

theorem sym1119_N_fix (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hra : r * a = a * r) (hg3 : g ^ 3 = 1)
    (hs : Subgroup.zpowers s = Subgroup.zpowers c) (hord : orderOf x = 27)
    {f : G} (hf : f ∈ Subgroup.closure ({a, c} : Set G)) (hfc : f ∉ Subgroup.zpowers c)
    (hr3 : r ^ 3 = f) {n : G} (hnP : n ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G))
    (hnA : n ∈ Subgroup.normalizer (A : Set G))
    (hnd : n ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    n * x ^ 3 * n⁻¹ ∈ sym1119W0 A x ∧ n * r * n⁻¹ * r⁻¹ ∈ sym1119W0 A x := by
  have hAy := sym1119_A_comm_y h45 h
  have hAr := sym1119_A_comm_r h113 h117 h hra
  have hAexp : ∀ u ∈ A, u ^ 3 = 1 := fun u hu => Item1117Proof.pow_three_of_mem_A h hu
  have hAcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    Item1117Proof.commute_of_mem_A h hu hv
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hfA : f ∈ A := sym1119_closure_ac_le_A h hf
  have hd1 : d ≠ 1 := sym1119_d_ne_one h
  have hzd : Subgroup.zpowers d = Subgroup.zpowers (x ^ 9) :=
    Item1119Sym.zpowers_eq_of_orderOf x d hord (Item1115Proof.d_mem_zpowers_x h)
      (Item1117Proof.orderOf_d h)
  have hx9 : x ^ 9 ≠ 1 := by
    intro h9
    have := orderOf_dvd_of_pow_eq_one h9
    rw [hord] at this
    norm_num at this
  have hy3 : (x ^ 3) ^ 3 ∈ Subgroup.zpowers d := by
    rw [← pow_mul]; exact hzd ▸ Subgroup.mem_zpowers _
  have hfd : f ∉ Subgroup.zpowers d := fun hfd =>
    hfc (((sym1119_indep h).2.2.2.1 f hf hfd) ▸ Subgroup.one_mem _)
  obtain ⟨-, hyr, hyr1⟩ := sym1119_yr_facts h45 h113 h117 h hord hf hfc hr3
  have hk : x ^ 3 * r * (x ^ 3)⁻¹ * r⁻¹ ∈ A := Subgroup.zpowers_le.mpr hdA hyr
  have hyP : x ^ 3 ∈ sec11P R g :=
    Item1119Proof.R_le_P R g (Subgroup.pow_mem _ (sym1119_x_mem_R h) 3)
  have hrP : r ∈ sec11P R g := Item1119Proof.R_le_P R g (sym1119_r_mem_R h)
  have hndd : n * d * n⁻¹ ∈ Subgroup.zpowers d :=
    (Subgroup.mem_normalizer_iff.mp hnd d).mp (Subgroup.mem_zpowers d)
  have hnA' : ∀ u ∈ A, n⁻¹ * u * n ∈ A := by
    intro u hu
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnA) u).mp hu
    simpa using this
  have hmem : ∀ w : G, w ∈ sec11P R g → (∀ u ∈ A, u * w = w * u) →
      n * w * n⁻¹ ∈ sym1119M A x r := by
    intro w hwP hwA
    have hC : n * w * n⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact sym1119_conj_comm (hwA _ (hnA' u hu))
    exact sym1119_CP_A_le h45 h113 h117 h hra hg3 hs
      ⟨(Subgroup.mem_normalizer_iff.mp hnP w).mp hwP, hC⟩
  have hny := Item1119Sym.mem_closure_normal_form A (x ^ 3) r hAy hAr hk
    (hmem (x ^ 3) hyP hAy)
  have hnr := Item1119Sym.mem_closure_normal_form A (x ^ 3) r hAy hAr hk (hmem r hrP hAr)
  have hy3ne : (x ^ 3) ^ 3 ≠ 1 := by rw [← pow_mul]; exact hx9
  obtain ⟨h1, h2⟩ := Item1119Sym.fix_r A (x ^ 3) r d f n hAexp hAcomm hAy hAr hdA hfA hd1 hy3
    hy3ne hr3 hfd hyr hyr1 hndd hny hnr
  obtain ⟨i, u, hu, e1⟩ := h1
  obtain ⟨i', u', hu', e2⟩ := h2
  exact ⟨(sym1119_mem_W0_iff h45 h).mpr ⟨i, u, hu, e1⟩, (sym1119_mem_W0_iff h45 h).mpr ⟨i', u', hu', e2⟩⟩

end Facts

end CFSG.RankThree.PartTwo.Sec11

end
