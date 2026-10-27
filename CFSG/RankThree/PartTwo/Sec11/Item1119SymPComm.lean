module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymStruct
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolGrOmega

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.GH74.GLS (oResidual)

section Facts


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem sym1119_P_eq_closure (h : Sec11Data G A c L a R Y d x s r g) :
    sec11P R g = Subgroup.closure ({r, x, s, g} : Set G) := by
  unfold sec11P
  rw [h.R_eq, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1
  ext y
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem sym1119_A_le_P (h : Sec11Data G A c L a R Y d x s r g) : A ≤ sec11P R g :=
  (Item1115Proof.A_le_R h.toHyp91).trans (Item1119Proof.R_le_P R g)

theorem sym1119_W0_le_P (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) :
    sym1119W0 A x ≤ sec11P R g := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y (hy | rfl)
  · exact sym1119_A_le_P h hy
  · exact Item1119Proof.R_le_P R g (Subgroup.pow_mem _ (sym1119_x_mem_R h) 3)

theorem sym1119_A_le_W0 (A : Subgroup G) (x : G) : A ≤ sym1119W0 A x := fun u hu =>
  Subgroup.subset_closure (Or.inl hu)

theorem sym1119_y_mem_W0 (A : Subgroup G) (x : G) : x ^ 3 ∈ sym1119W0 A x :=
  Subgroup.subset_closure (Or.inr (by simp))

theorem sym1119_r_not_mem_W0 (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hyr1 : x ^ 3 * r * (x ^ 3)⁻¹ * r⁻¹ ≠ 1) : r ∉ sym1119W0 A x := by
  intro hr
  obtain ⟨i, u, hu, e⟩ := (sym1119_mem_W0_iff h45 h).mp hr
  apply hyr1
  have hy : (x ^ 3) * r = r * (x ^ 3) := by
    rw [e]
    have h1 : (x ^ 3) * (x ^ 3) ^ i = (x ^ 3) ^ i * (x ^ 3) :=
      ((Commute.refl (x ^ 3)).zpow_right i).eq
    have h2 : (x ^ 3) * u = u * (x ^ 3) := (sym1119_A_comm_y h45 h u hu).symm
    calc x ^ 3 * ((x ^ 3) ^ i * u) = (x ^ 3) ^ i * (x ^ 3 * u) := by rw [← mul_assoc, h1, mul_assoc]
      _ = (x ^ 3) ^ i * (u * x ^ 3) := by rw [h2]
      _ = ((x ^ 3) ^ i * u) * x ^ 3 := by rw [mul_assoc]
  rw [hy]; group
theorem sym1119_conj_comm_of_comm {g a y : G} (hga : g * a = a * g) (hya : y * a = a * y) :
    (g * y * g⁻¹) * a = a * (g * y * g⁻¹) := by
  have h1 : g⁻¹ * a = a * g⁻¹ := by
    calc g⁻¹ * a = g⁻¹ * (a * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * a) * g⁻¹ := by rw [hga]
      _ = a * g⁻¹ := by group
  calc (g * y * g⁻¹) * a = g * y * (g⁻¹ * a) := by group
    _ = g * y * (a * g⁻¹) := by rw [h1]
    _ = g * (y * a) * g⁻¹ := by group
    _ = g * (a * y) * g⁻¹ := by rw [hya]
    _ = (g * a) * y * g⁻¹ := by group
    _ = (a * g) * y * g⁻¹ := by rw [hga]
    _ = a * (g * y * g⁻¹) := by group

theorem sym1119_comm_symm {W : Subgroup G} {u v : G} (h : u * v * u⁻¹ * v⁻¹ ∈ W) :
    v * u * v⁻¹ * u⁻¹ ∈ W := by
  have e : v * u * v⁻¹ * u⁻¹ = (u * v * u⁻¹ * v⁻¹)⁻¹ := by group
  rw [e]; exact W.inv_mem h

theorem sym1119_comm_self (W : Subgroup G) (u : G) : u * u * u⁻¹ * u⁻¹ ∈ W := by
  have : u * u * u⁻¹ * u⁻¹ = 1 := by group
  rw [this]; exact W.one_mem

theorem sym1119_comm_of_mem_zpowers {u c s : G} (hs : s ∈ Subgroup.zpowers c) (huc : u * c = c * u) :
    u * s * u⁻¹ * s⁻¹ = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have : u * c ^ k = c ^ k * u := ((show Commute u c from huc).zpow_right k).eq
  rw [this]; group
theorem sym1119_g_conj_f (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) {κ : ℤ} (hgc : g * c * g⁻¹ = d ^ κ * c)
    {f : G} (hf : f ∈ Subgroup.closure ({a, c} : Set G)) :
    ∃ t : ℤ, g * f * g⁻¹ = d ^ t * f := by
  have hac : a * c = c * a := Item1117Proof.commute_of_mem_A h h.a_mem h.mem_A
  have had : a * d = d * a := Item1117Proof.commute_of_mem_A h h.a_mem (Item1117Proof.d_mem_A h)
  have hcd : c * d = d * c := Item1117Proof.commute_of_mem_A h h.mem_A (Item1117Proof.d_mem_A h)
  have hga : g * a = a * g := sym1119_g_comm_a h
  obtain ⟨i, j, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hac hf
  refine ⟨κ * j, ?_⟩
  have e1 : g * a ^ i * g⁻¹ = a ^ i := by
    rw [mul_inv_eq_iff_eq_mul]
    exact ((show Commute g a from hga).zpow_right i).eq
  have e2 : g * c ^ j * g⁻¹ = (d ^ κ * c) ^ j := by rw [← hgc, conj_zpow]
  have e3 : (d ^ κ * c) ^ j = d ^ (κ * j) * c ^ j := by
    rw [Commute.mul_zpow ((show Commute d c from hcd.symm).zpow_left κ), ← zpow_mul]
  calc g * (a ^ i * c ^ j) * g⁻¹ = (g * a ^ i * g⁻¹) * (g * c ^ j * g⁻¹) := by group
    _ = a ^ i * (d ^ (κ * j) * c ^ j) := by rw [e1, e2, e3]
    _ = d ^ (κ * j) * (a ^ i * c ^ j) := by
        rw [← mul_assoc, ← mul_assoc]
        congr 1
        exact ((show Commute a d from had).zpow_zpow i (κ * j)).eq

theorem sym1119_VW (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hs : Subgroup.zpowers s = Subgroup.zpowers c) {p : G}
    (hp : p ∈ Subgroup.closure ({s, x, a} : Set G)) (hpa : p * a = a * p) :
    p ∈ sym1119W0 A x := by
  obtain ⟨m, hm, hxa⟩ := sym1119_x_a_action h45 h
  obtain ⟨hxc, hxd⟩ := sym1119_x_comm h45 h
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h hdA
  have hd1 : d ≠ 1 := sym1119_d_ne_one h
  have had : a * d = d * a := Item1117Proof.commute_of_mem_A h h.a_mem hdA
  have hca : c * a = a * c := Item1117Proof.commute_of_mem_A h h.mem_A h.a_mem
  have haR : a ∈ R := Item1115Proof.A_le_R h.toHyp91 h.a_mem
  have hux : a * x * a⁻¹ ∈ Subgroup.zpowers x :=
    (Subgroup.mem_normalizer_iff.mp (Item1115Proof.mem_normalizer_zpowers_x h45 h haR) x).mp
      (Subgroup.mem_zpowers x)
  have hux' : a⁻¹ * x * a ∈ Subgroup.zpowers x := by
    have := (Subgroup.mem_normalizer_iff.mp
      (Item1115Proof.mem_normalizer_zpowers_x h45 h (R.inv_mem haR)) x).mp (Subgroup.mem_zpowers x)
    simpa using this
  have hscl : s ∈ Subgroup.zpowers c := hs ▸ Subgroup.mem_zpowers s
  have hVle : Subgroup.closure ({s, x, a} : Set G) ≤ Subgroup.closure ({a, x, c} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (rfl | rfl | rfl)
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hscl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  obtain ⟨j, i, l, hpe⟩ := Item1119Sym.commute_a_triple_form a x c a d m hca hxc.symm hca hux hux'
    rfl hxa hxd had hd3 hd1 hm (hVle hp) hpa
  rw [hpe]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.zpow_mem _
    (sym1119_A_le_W0 A x h.a_mem) _) (Subgroup.zpow_mem _ (sym1119_y_mem_W0 A x) _))
    (Subgroup.zpow_mem _ (sym1119_A_le_W0 A x h.mem_A) _)
theorem sym1119_r_norm_W0 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hra : r * a = a * r)
    (hyr : x ^ 3 * r * (x ^ 3)⁻¹ * r⁻¹ ∈ Subgroup.zpowers d) :
    r ∈ Subgroup.normalizer ((sym1119W0 A x : Subgroup G) : Set G) := by
  have hAr := sym1119_A_comm_r h113 h117 h hra
  have hdzW : Subgroup.zpowers d ≤ sym1119W0 A x :=
    Subgroup.zpowers_le.mpr (sym1119_A_le_W0 A x (Item1117Proof.d_mem_A h))
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  refine Item1119Sym.conj_mem_closure_of_gens ((A : Set G) ∪ {x ^ 3}) (sym1119W0 A x) r ?_ hw
  rintro u (hu | hu)
  · have : r * u * r⁻¹ = u := by
      rw [mul_inv_eq_iff_eq_mul]; exact (hAr u hu).symm
    rw [this]; exact sym1119_A_le_W0 A x hu
  · rw [Set.mem_singleton_iff] at hu
    rw [hu]
    have e : r * x ^ 3 * r⁻¹ = (x ^ 3 * r * (x ^ 3)⁻¹ * r⁻¹)⁻¹ * x ^ 3 := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hdzW hyr)) (sym1119_y_mem_W0 A x)

theorem sym1119_x_norm_W0 (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) :
    x ∈ Subgroup.normalizer ((sym1119W0 A x : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  refine Item1119Sym.conj_mem_closure_of_gens ((A : Set G) ∪ {x ^ 3}) (sym1119W0 A x) x ?_ hw
  rintro u (hu | hu)
  · exact sym1119_A_le_W0 A x ((Subgroup.mem_normalizer_iff.mp hxA u).mp hu)
  · rw [Set.mem_singleton_iff] at hu
    rw [hu]
    have : x * x ^ 3 * x⁻¹ = x ^ 3 := by group
    rw [this]; exact sym1119_y_mem_W0 A x

theorem sym1119_g_norm_W0 (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hs : Subgroup.zpowers s = Subgroup.zpowers c)
    (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgV : g ∈ Subgroup.normalizer ((Subgroup.closure ({s, x, a} : Set G) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((sym1119W0 A x : Subgroup G) : Set G) := by
  have hAy := sym1119_A_comm_y h45 h
  have hga : g * a = a * g := sym1119_g_comm_a h
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  refine Item1119Sym.conj_mem_closure_of_gens ((A : Set G) ∪ {x ^ 3}) (sym1119W0 A x) g ?_ hw
  rintro u (hu | hu)
  · exact sym1119_A_le_W0 A x ((Subgroup.mem_normalizer_iff.mp hgA u).mp hu)
  · rw [Set.mem_singleton_iff] at hu
    rw [hu]
    have hxV : x ∈ Subgroup.closure ({s, x, a} : Set G) := Subgroup.subset_closure (by simp)
    have h1 : g * x * g⁻¹ ∈ Subgroup.closure ({s, x, a} : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hgV x).mp hxV
    have h2 : g * x ^ 3 * g⁻¹ ∈ Subgroup.closure ({s, x, a} : Set G) := by
      rw [← conj_pow]; exact Subgroup.pow_mem _ h1 3
    exact sym1119_VW h45 h hs h2 (sym1119_conj_comm_of_comm hga (hAy a h.a_mem).symm)
theorem sym1119_conj_mem_M (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hra : r * a = a * r) (hg3 : g ^ 3 = 1)
    (hs : Subgroup.zpowers s = Subgroup.zpowers c) {n w : G}
    (hnP : n ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G))
    (hnA : n ∈ Subgroup.normalizer (A : Set G)) (hwP : w ∈ sec11P R g)
    (hwA : ∀ u ∈ A, u * w = w * u) : n * w * n⁻¹ ∈ sym1119M A x r := by
  have hnA' : ∀ u ∈ A, n⁻¹ * u * n ∈ A := by
    intro u hu
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnA) u).mp hu
    simpa using this
  have hC : n * w * n⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact sym1119_conj_comm (hwA _ (hnA' u hu))
  exact sym1119_CP_A_le h45 h113 h117 h hra hg3 hs
    ⟨(Subgroup.mem_normalizer_iff.mp hnP w).mp hwP, hC⟩

theorem sym1119_comm_rg_mem_W0 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hra : r * a = a * r) (hg3 : g ^ 3 = 1)
    (hs : Subgroup.zpowers s = Subgroup.zpowers c) (hord : orderOf x = 27)
    {f : G} (hf : f ∈ Subgroup.closure ({a, c} : Set G)) (hfc : f ∉ Subgroup.zpowers c)
    (hr3 : r ^ 3 = f) (hgA : g ∈ Subgroup.normalizer (A : Set G)) :
    r * g * r⁻¹ * g⁻¹ ∈ sym1119W0 A x := by
  obtain ⟨κ, hκ, hgc⟩ := sym1119_g_c_action h113 h117 h
  obtain ⟨t, hgf⟩ := sym1119_g_conj_f h113 h117 h hgc hf
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
  have hy3 : (x ^ 3) ^ 3 ∈ Subgroup.zpowers d := by
    rw [← pow_mul]; exact hzd ▸ Subgroup.mem_zpowers _
  have hfd : f ∉ Subgroup.zpowers d := fun hfd =>
    hfc (((sym1119_indep h).2.2.2.1 f hf hfd) ▸ Subgroup.one_mem _)
  obtain ⟨-, hyr, hyr1⟩ := sym1119_yr_facts h45 h113 h117 h hord hf hfc hr3
  have hk : x ^ 3 * r * (x ^ 3)⁻¹ * r⁻¹ ∈ A := Subgroup.zpowers_le.mpr hdA hyr
  have hgP : g ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (Item1119Proof.g_mem_P R g)
  have hrP : r ∈ sec11P R g := Item1119Proof.R_le_P R g (sym1119_r_mem_R h)
  have hgr := Item1119Sym.mem_closure_normal_form A (x ^ 3) r hAy hAr hk
    (sym1119_conj_mem_M h45 h113 h117 h hra hg3 hs hgP hgA hrP hAr)
  obtain ⟨i, u, hu, e⟩ := Item1119Sym.g_r_comm_mem A (x ^ 3) r d f g hAexp hAcomm hAy hAr hdA hfA
    hd1 hy3 hr3 hfd hyr t hgf hgr
  have hW : g * r * g⁻¹ * r⁻¹ ∈ sym1119W0 A x :=
    (sym1119_mem_W0_iff h45 h).mpr ⟨i, u, hu, e⟩
  exact sym1119_comm_symm hW

theorem sym1119_comm_xg_mem_W0 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g)
    (hs : Subgroup.zpowers s = Subgroup.zpowers c)
    (hgV : g ∈ Subgroup.normalizer ((Subgroup.closure ({s, x, a} : Set G) : Subgroup G) : Set G)) :
    x * g * x⁻¹ * g⁻¹ ∈ sym1119W0 A x := by
  obtain ⟨κ, hκ, hgc⟩ := sym1119_g_c_action h113 h117 h
  obtain ⟨m, hm, hxa⟩ := sym1119_x_a_action h45 h
  obtain ⟨hxc, hxd⟩ := sym1119_x_comm h45 h
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hac : a * c = c * a := Item1117Proof.commute_of_mem_A h h.a_mem h.mem_A
  have had : a * d = d * a := Item1117Proof.commute_of_mem_A h h.a_mem hdA
  have hcd : c * d = d * c := Item1117Proof.commute_of_mem_A h h.mem_A hdA
  have hga : g * a = a * g := sym1119_g_comm_a h
  have hgd : g * d = d * g :=
    Item1119Proof.commute_of_mem_zpowers_d h113 h117 h (Subgroup.mem_zpowers d)
      (Item1119Proof.g_mem_P R g)
  have hcentral := Item1119Sym.commutator_xg_comm x g a c d m κ hxa hxc hxd hga hgc hgd hac had hcd
  have hxV : x ∈ Subgroup.closure ({s, x, a} : Set G) := Subgroup.subset_closure (by simp)
  have h1 : g * x⁻¹ * g⁻¹ ∈ Subgroup.closure ({s, x, a} : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hgV x⁻¹).mp (Subgroup.inv_mem _ hxV)
  have hpV : x * g * x⁻¹ * g⁻¹ ∈ Subgroup.closure ({s, x, a} : Set G) := by
    have e : x * g * x⁻¹ * g⁻¹ = x * (g * x⁻¹ * g⁻¹) := by group
    rw [e]; exact Subgroup.mul_mem _ hxV h1
  have haA : a ∈ Subgroup.closure ({c, a, d} : Set G) := Subgroup.subset_closure (by simp)
  exact sym1119_VW h45 h hs hpV (hcentral a haA)
theorem sym1119_PP_le_W0 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hra : r * a = a * r) (hg3 : g ^ 3 = 1)
    (hs : Subgroup.zpowers s = Subgroup.zpowers c) (hord : orderOf x = 27)
    {f : G} (hf : f ∈ Subgroup.closure ({a, c} : Set G)) (hfc : f ∉ Subgroup.zpowers c)
    (hr3 : r ^ 3 = f) (hPA : sec11P R g ≤ Subgroup.normalizer (A : Set G))
    (hV : sec11P R g ≤
      Subgroup.normalizer ((Subgroup.closure ({s, x, a} : Set G) : Subgroup G) : Set G)) :
    ⁅sec11P R g, sec11P R g⁆ ≤ sym1119W0 A x := by
  obtain ⟨hrx, hyr, hyr1⟩ := sym1119_yr_facts h45 h113 h117 h hord hf hfc hr3
  obtain ⟨hxc, hxd⟩ := sym1119_x_comm h45 h
  have hscl : s ∈ Subgroup.zpowers c := hs ▸ Subgroup.mem_zpowers s
  have hscA : s ∈ A := Subgroup.zpowers_le.mpr h.mem_A hscl
  have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g (sym1119_x_mem_R h)
  have hgP : g ∈ sec11P R g := Item1119Proof.g_mem_P R g
  have hrR := sym1119_r_mem_R h
  have hrx' : r * x * r⁻¹ * x⁻¹ ∈ sym1119W0 A x :=
    (Subgroup.zpowers_le.mpr (sym1119_y_mem_W0 A x)) hrx
  have hrs : r * s * r⁻¹ * s⁻¹ ∈ sym1119W0 A x := by
    rw [sym1119_comm_of_mem_zpowers hscl (sym1119_R_comm_c h r hrR)]; exact Subgroup.one_mem _
  have hxs : x * s * x⁻¹ * s⁻¹ ∈ sym1119W0 A x := by
    rw [sym1119_comm_of_mem_zpowers hscl hxc]; exact Subgroup.one_mem _
  have hsg : s * g * s⁻¹ * g⁻¹ ∈ sym1119W0 A x := by
    have e : s * g * s⁻¹ * g⁻¹ = s * (g * s⁻¹ * g⁻¹) := by group
    rw [e]
    exact sym1119_A_le_W0 A x (A.mul_mem hscA
      ((Subgroup.mem_normalizer_iff.mp (hPA hgP) s⁻¹).mp (A.inv_mem hscA)))
  have hrg := sym1119_comm_rg_mem_W0 h45 h113 h117 h hra hg3 hs hord hf hfc hr3 (hPA hgP)
  have hxg := sym1119_comm_xg_mem_W0 h45 h113 h117 h hs (hV hgP)
  rw [sym1119_P_eq_closure h]
  refine commutator_closure_le (T := ({r, x, s, g} : Set G)) (V := sym1119W0 A x) ?_ ?_
  · refine (Subgroup.closure_le _).mpr ?_
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with ht | ht | ht | ht <;> rw [ht]
    · exact sym1119_r_norm_W0 h45 h113 h117 h hra hyr
    · exact sym1119_x_norm_W0 h45 h (hPA hxP)
    · exact Subgroup.le_normalizer (sym1119_A_le_W0 A x hscA)
    · exact sym1119_g_norm_W0 h45 h hs (hPA hgP) (hV hgP)
  · intro u hu v hv
    rw [commutatorElement_def]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with hu | hu | hu | hu <;> rcases hv with hv | hv | hv | hv <;> rw [hu, hv]
    · exact sym1119_comm_self _ _
    · exact hrx'
    · exact hrs
    · exact hrg
    · exact sym1119_comm_symm hrx'
    · exact sym1119_comm_self _ _
    · exact hxs
    · exact hxg
    · exact sym1119_comm_symm hrs
    · exact sym1119_comm_symm hxs
    · exact sym1119_comm_self _ _
    · exact hsg
    · exact sym1119_comm_symm hrg
    · exact sym1119_comm_symm hxg
    · exact sym1119_comm_symm hsg
    · exact sym1119_comm_self _ _


end Facts

end CFSG.RankThree.PartTwo.Sec11

end
