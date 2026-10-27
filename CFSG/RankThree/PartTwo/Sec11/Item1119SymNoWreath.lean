module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymPComm
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolIndexCard
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolCenterNormal
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolLineEq
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolWreathObs
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolWreathExp
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolCenterD

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.GH74.GLS (oResidual)

section Facts


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem sym1119_isPGroup_P (h : Sec11Data G A c L a R Y d x s r g) :
    IsPGroup 3 (sec11P R g) := fun q => by
  obtain ⟨k, hk⟩ := Item1119Proof.exists_pow_eq_one_of_mem_P h q.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem sym1119_A_lt_W0 (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hord : orderOf x = 27) : A < sym1119W0 A x := by
  refine lt_of_le_of_ne (sym1119_A_le_W0 A x) fun hAW => ?_
  have hy : x ^ 3 ∈ A := hAW ▸ sym1119_y_mem_W0 A x
  have h3 : (x ^ 3) ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h hy
  have h9 : x ^ 9 = 1 := by rw [← h3, ← pow_mul]
  have := orderOf_dvd_of_pow_eq_one h9
  rw [hord] at this
  norm_num at this

theorem sym1119_W0_lt_P (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hyr1 : x ^ 3 * r * (x ^ 3)⁻¹ * r⁻¹ ≠ 1) : sym1119W0 A x < sec11P R g := by
  refine lt_of_le_of_ne (sym1119_W0_le_P h45 h) fun hWP => ?_
  have hrP : r ∈ sec11P R g := Item1119Proof.R_le_P R g (sym1119_r_mem_R h)
  rw [← hWP] at hrP
  exact sym1119_r_not_mem_W0 h45 h hyr1 hrP

theorem sym1119_card_P_gt (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hord : orderOf x = 27) (hyr1 : x ^ 3 * r * (x ^ 3)⁻¹ * r⁻¹ ≠ 1) :
    81 < Nat.card (sec11P R g) := by
  have h1 := Item1119Sym.three_mul_card_le_of_lt A (sym1119W0 A x)
    ((sym1119_isPGroup_P h).to_le (sym1119_W0_le_P h45 h)) (sym1119_A_lt_W0 h45 h hord)
  have h2 := Item1119Sym.three_mul_card_le_of_lt (sym1119W0 A x) (sec11P R g)
    (sym1119_isPGroup_P h) (sym1119_W0_lt_P h45 h hyr1)
  have h27 : Nat.card A = 27 := h.card_eq
  omega
theorem sym1119_mem_zpowers_of_order_three {w d : G} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hwd : w ∈ Subgroup.zpowers d) :
    d ∈ Subgroup.zpowers w := by
  have h1 : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have h2 : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hle : Subgroup.zpowers w ≤ Subgroup.zpowers d := Subgroup.zpowers_le.mpr hwd
  have heq : Subgroup.zpowers w = Subgroup.zpowers d := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, Nat.card_zpowers, h1, h2]
  rw [heq]; exact Subgroup.mem_zpowers d

theorem sym1119_d_mem_K (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hra : r * a = a * r) (hg3 : g ^ 3 = 1)
    (hs : Subgroup.zpowers s = Subgroup.zpowers c) (hord : orderOf x = 27)
    {f : G} (hf : f ∈ Subgroup.closure ({a, c} : Set G)) (hfc : f ∉ Subgroup.zpowers c)
    (hr3 : r ^ 3 = f) (K : Subgroup (sec11P R g)) [K.Normal] (hK : K ≠ ⊥) :
    (⟨d, sym1119_A_le_P h (Item1117Proof.d_mem_A h)⟩ : sec11P R g) ∈ K := by
  obtain ⟨κ, hκ, hgc⟩ := sym1119_g_c_action h113 h117 h
  obtain ⟨m, hm, hxa⟩ := sym1119_x_a_action h45 h
  obtain ⟨hxc, hxd⟩ := sym1119_x_comm h45 h
  have hAy := sym1119_A_comm_y h45 h
  have hAr := sym1119_A_comm_r h113 h117 h hra
  have hAexp : ∀ u ∈ A, u ^ 3 = 1 := fun u hu => Item1117Proof.pow_three_of_mem_A h hu
  have hAcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    Item1117Proof.commute_of_mem_A h hu hv
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hfA : f ∈ A := sym1119_closure_ac_le_A h hf
  have hd1 : d ≠ 1 := sym1119_d_ne_one h
  have hd3 : d ^ 3 = 1 := hAexp d hdA
  have hac : a * c = c * a := Item1117Proof.commute_of_mem_A h h.a_mem h.mem_A
  have had : a * d = d * a := Item1117Proof.commute_of_mem_A h h.a_mem hdA
  have hcd : c * d = d * c := Item1117Proof.commute_of_mem_A h h.mem_A hdA
  have hga : g * a = a * g := sym1119_g_comm_a h
  have hgd : g * d = d * g :=
    Item1119Proof.commute_of_mem_zpowers_d h113 h117 h (Subgroup.mem_zpowers d)
      (Item1119Proof.g_mem_P R g)
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
  have hy3ne : (x ^ 3) ^ 3 ≠ 1 := by rw [← pow_mul]; exact hx9
  have hfd : f ∉ Subgroup.zpowers d := fun hfd =>
    hfc (((sym1119_indep h).2.2.2.1 f hf hfd) ▸ Subgroup.one_mem _)
  obtain ⟨-, hyr, hyr1⟩ := sym1119_yr_facts h45 h113 h117 h hord hf hfc hr3
  have hk : x ^ 3 * r * (x ^ 3)⁻¹ * r⁻¹ ∈ A := Subgroup.zpowers_le.mpr hdA hyr
  have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g (sym1119_x_mem_R h)
  have hgP : g ∈ sec11P R g := Item1119Proof.g_mem_P R g
  obtain ⟨z, hzK, hz1, hzc⟩ := Item1119Sym.exists_ne_one_mem_center_of_normal (sec11P R g)
    (sym1119_isPGroup_P h) K hK
  obtain ⟨n, hn⟩ := Item1119Sym.exists_pow_orderOf_eq_three z hz1 (sym1119_isPGroup_P h z)
  have hwK : z ^ n ∈ K := K.pow_mem hzK n
  have hwc : z ^ n ∈ Subgroup.center (sec11P R g) := Subgroup.pow_mem _ hzc n
  have hw3 : (z ^ n) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (z ^ n)
    rwa [hn] at this
  have hw1 : z ^ n ≠ 1 := fun h1 => by rw [h1] at hn; simp at hn
  set w : sec11P R g := z ^ n with hwdef
  have hwG3 : ((w : G)) ^ 3 = 1 := by simpa using congrArg Subtype.val hw3
  have hwG1 : (w : G) ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
  have hwcomm : ∀ q ∈ sec11P R g, (w : G) * q = q * (w : G) := fun q hq => by
    have := Subgroup.mem_center_iff.mp hwc ⟨q, hq⟩
    exact (congrArg Subtype.val this).symm
  have hwM : (w : G) ∈ sym1119M A x r := by
    have hC : (w : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (hwcomm u (sym1119_A_le_P h hu)).symm
    exact sym1119_CP_A_le h45 h113 h117 h hra hg3 hs ⟨w.2, hC⟩
  obtain ⟨i, j, u, hu, hwe⟩ := Item1119Sym.mem_closure_normal_form A (x ^ 3) r hAy hAr hk hwM
  have hwA : (w : G) ∈ A := by
    rw [hwe]
    refine Item1119Sym.mem_A_of_cube_eq_one A (x ^ 3) r d f hAexp hAcomm hAy hAr hdA hfA hd1 hy3
      hy3ne hr3 hfd hyr i j u hu ?_
    rw [← hwe]; exact hwG3
  have hwcl : (w : G) ∈ Subgroup.closure ({c, a, d} : Set G) := h.closure_eq ▸ hwA
  have hwd : (w : G) ∈ Subgroup.zpowers d :=
    Item1119Sym.mem_zpowers_d_of_central x g a c d (w : G) m κ hxa hm hxc hxd hga hgc hκ hgd hac
      had hcd (hAexp a h.a_mem) (hAexp c h.mem_A) hd3 hd1 hwcl (hwcomm x hxP).symm
      (hwcomm g hgP).symm
  have hdw : d ∈ Subgroup.zpowers (w : G) :=
    sym1119_mem_zpowers_of_order_three hwG3 hwG1 hd3 hd1 hwd
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdw
  have : (⟨d, sym1119_A_le_P h hdA⟩ : sec11P R g) = w ^ k := by
    apply Subtype.ext
    simp [hk]
  rw [this]
  exact K.zpow_mem hwK k
theorem sym1119_comm_A_P (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g)
    (hA2 : A ≤ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype)
    (hPA : sec11P R g ≤ Subgroup.normalizer (A : Set G)) {u p : G} (hu : u ∈ A)
    (hp : p ∈ sec11P R g) : u * p * u⁻¹ * p⁻¹ ∈ Subgroup.zpowers d := by
  obtain ⟨κ, hκ, hgc⟩ := sym1119_g_c_action h113 h117 h
  obtain ⟨m, hm, hxa⟩ := sym1119_x_a_action h45 h
  obtain ⟨hxc, hxd⟩ := sym1119_x_comm h45 h
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h hdA
  have hd1 : d ≠ 1 := sym1119_d_ne_one h
  have hac : a * c = c * a := Item1117Proof.commute_of_mem_A h h.a_mem h.mem_A
  have had : a * d = d * a := Item1117Proof.commute_of_mem_A h h.a_mem hdA
  have hcd : c * d = d * c := Item1117Proof.commute_of_mem_A h h.mem_A hdA
  have hga : g * a = a * g := sym1119_g_comm_a h
  have hgd : g * d = d * g :=
    Item1119Proof.commute_of_mem_zpowers_d h113 h117 h (Subgroup.mem_zpowers d)
      (Item1119Proof.g_mem_P R g)
  have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g (sym1119_x_mem_R h)
  have hgP : g ∈ sec11P R g := Item1119Proof.g_mem_P R g
  have hA : u * p * u⁻¹ * p⁻¹ ∈ A := by
    have e : u * p * u⁻¹ * p⁻¹ = u * (p * u⁻¹ * p⁻¹) := by group
    rw [e]
    exact A.mul_mem hu ((Subgroup.mem_normalizer_iff.mp (hPA hp) u⁻¹).mp (A.inv_mem hu))
  obtain ⟨ũ, hũ, rfl⟩ := hA2 hu
  have hcen : ∀ q : G, q ∈ sec11P R g → q * (ũ * p * ũ⁻¹ * p⁻¹) = (ũ * p * ũ⁻¹ * p⁻¹) * q := by
    intro q hq
    have h2 := (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mp hũ ⟨p, hp⟩
    rw [Subgroup.upperCentralSeries_one] at h2
    have h3 := Subgroup.mem_center_iff.mp h2 ⟨q, hq⟩
    simpa [commutatorElement_def] using congrArg Subtype.val h3
  refine Item1119Sym.mem_zpowers_d_of_central x g a c d _ m κ hxa hm hxc hxd hga hgc hκ hgd hac
    had hcd (Item1117Proof.pow_three_of_mem_A h h.a_mem) (Item1117Proof.pow_three_of_mem_A h h.mem_A)
    hd3 hd1 (h.closure_eq ▸ hA) (hcen x hxP) (hcen g hgP)
theorem sym1119_noWreath (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hra : r * a = a * r) (hg3 : g ^ 3 = 1)
    (hs : Subgroup.zpowers s = Subgroup.zpowers c) (hord : orderOf x = 27)
    {f : G} (hf : f ∈ Subgroup.closure ({a, c} : Set G)) (hfc : f ∉ Subgroup.zpowers c)
    (hr3 : r ^ 3 = f)
    (hA2 : A ≤ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype)
    (hPA : sec11P R g ≤ Subgroup.normalizer (A : Set G))
    (hV : sec11P R g ≤
      Subgroup.normalizer ((Subgroup.closure ({s, x, a} : Set G) : Subgroup G) : Set G))
    (hPP : ⁅sec11P R g, sec11P R g⁆ ≤ sym1119W0 A x)
    (K : Subgroup (sec11P R g)) [K.Normal] : IsEmpty (sec11P R g ⧸ K ≃* W33) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨hrx, hyr, hyr1⟩ := sym1119_yr_facts h45 h113 h117 h hord hf hfc hr3
  obtain ⟨m, hm, hxa⟩ := sym1119_x_a_action h45 h
  obtain ⟨hxc, hxd⟩ := sym1119_x_comm h45 h
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hdP : d ∈ sec11P R g := sym1119_A_le_P h hdA
  have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g (sym1119_x_mem_R h)
  have hrP : r ∈ sec11P R g := Item1119Proof.R_le_P R g (sym1119_r_mem_R h)
  have hsP : s ∈ sec11P R g := Item1119Proof.R_le_P R g (sym1119_s_mem_R h)
  have hgP : g ∈ sec11P R g := Item1119Proof.g_mem_P R g
  have haP : a ∈ sec11P R g := sym1119_A_le_P h h.a_mem
  have hscl : s ∈ Subgroup.zpowers c := hs ▸ Subgroup.mem_zpowers s
  have hrR := sym1119_r_mem_R h
  have hK : K ≠ ⊥ := by
    intro hKbot
    have hcardQ : Nat.card (sec11P R g ⧸ K) = 81 := (Nat.card_congr e.toEquiv).trans card_wreath
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    have hKcard : Nat.card K = 1 := by rw [hKbot]; exact Subgroup.card_bot
    rw [hcardQ, hKcard] at h1
    have h2 := sym1119_card_P_gt h45 h hord hyr1
    omega
  have hdK := sym1119_d_mem_K h45 h113 h117 h hra hg3 hs hord hf hfc hr3 K hK
  set K' : Subgroup G := K.map (sec11P R g).subtype with hK'def
  have hK'mem : ∀ (w : G) (hw : w ∈ sec11P R g), w ∈ K' ↔ (⟨w, hw⟩ : sec11P R g) ∈ K := by
    intro w hw
    constructor
    · rintro ⟨k, hk, hkw⟩
      have : k = ⟨w, hw⟩ := Subtype.ext hkw
      rwa [this] at hk
    · intro hk; exact ⟨⟨w, hw⟩, hk, rfl⟩
  have hK'n : ∀ p ∈ sec11P R g, ∀ k ∈ K', p * k * p⁻¹ ∈ K' := by
    intro p hp k hk
    obtain ⟨k0, hk0, rfl⟩ := hk
    exact ⟨⟨p, hp⟩ * k0 * ⟨p, hp⟩⁻¹, (inferInstance : K.Normal).conj_mem k0 hk0 ⟨p, hp⟩, by simp⟩
  have hdK' : d ∈ K' := (hK'mem d hdP).mpr hdK
  have hdzK' : Subgroup.zpowers d ≤ K' := Subgroup.zpowers_le.mpr hdK'
  have hK'norm : ∀ t ∈ sec11P R g, t ∈ Subgroup.normalizer (K' : Set G) := fun t ht =>
    Subgroup.mem_normalizer_fintype fun k hk => hK'n t ht k hk
  have hxa1 : x * a * x⁻¹ * a⁻¹ ∈ K' := by
    have : x * a * x⁻¹ * a⁻¹ = d ^ m := by rw [hxa]; group
    rw [this]; exact hdzK' (Subgroup.zpow_mem _ (Subgroup.mem_zpowers d) m)
  have hxs1 : x * s * x⁻¹ * s⁻¹ ∈ K' := by
    rw [sym1119_comm_of_mem_zpowers hscl hxc]; exact K'.one_mem
  have has1 : a * s * a⁻¹ * s⁻¹ ∈ K' := by
    rw [sym1119_comm_of_mem_zpowers hscl (Item1117Proof.commute_of_mem_A h h.a_mem h.mem_A)]
    exact K'.one_mem
  have hVcomm : ⁅Subgroup.closure ({s, x, a} : Set G), Subgroup.closure ({s, x, a} : Set G)⁆ ≤
      K' := by
    refine commutator_closure_le (T := ({s, x, a} : Set G)) (V := K') ?_ ?_
    · refine (Subgroup.closure_le _).mpr ?_
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with ht | ht | ht <;> rw [ht]
      · exact hK'norm s hsP
      · exact hK'norm x hxP
      · exact hK'norm a haP
    · intro u hu v hv
      rw [commutatorElement_def]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rw [hu, hv]
      · exact sym1119_comm_self _ _
      · exact sym1119_comm_symm hxs1
      · exact sym1119_comm_symm has1
      · exact hxs1
      · exact sym1119_comm_self _ _
      · exact hxa1
      · exact has1
      · exact sym1119_comm_symm hxa1
      · exact sym1119_comm_self _ _
  have hxK : x ^ 3 ∈ K' := by
    have hVn : ∀ p : sec11P R g, ∀ v ∈ (Subgroup.closure ({s, x, a} : Set G)).subgroupOf
        (sec11P R g), p * v * p⁻¹ ∈ (Subgroup.closure ({s, x, a} : Set G)).subgroupOf
        (sec11P R g) := by
      intro p v hv
      rw [Subgroup.mem_subgroupOf] at hv ⊢
      simpa using (Subgroup.mem_normalizer_iff.mp (hV p.2) v).mp hv
    have hVc : ∀ u ∈ (Subgroup.closure ({s, x, a} : Set G)).subgroupOf (sec11P R g),
        ∀ v ∈ (Subgroup.closure ({s, x, a} : Set G)).subgroupOf (sec11P R g),
        u * v * u⁻¹ * v⁻¹ ∈ K := by
      intro u hu v hv
      rw [Subgroup.mem_subgroupOf] at hu hv
      have h1 : (u : G) * v * (u : G)⁻¹ * (v : G)⁻¹ ∈ K' := by
        have := hVcomm (Subgroup.commutator_mem_commutator hu hv)
        rwa [commutatorElement_def] at this
      have e1 : (⟨(u : G) * v * (u : G)⁻¹ * (v : G)⁻¹, (u * v * u⁻¹ * v⁻¹).2⟩ :
          sec11P R g) = u * v * u⁻¹ * v⁻¹ := Subtype.ext rfl
      have h2 := (hK'mem ((u : G) * v * (u : G)⁻¹ * (v : G)⁻¹) (u * v * u⁻¹ * v⁻¹).2).mp h1
      rwa [e1] at h2
    have h3 := Item1119Sym.pow_three_mem_of_abelian_normal e
      ((Subgroup.closure ({s, x, a} : Set G)).subgroupOf (sec11P R g)) hVn hVc ⟨x, hxP⟩
      (by rw [Subgroup.mem_subgroupOf]; exact Subgroup.subset_closure (by simp))
    exact (hK'mem (x ^ 3) (Subgroup.pow_mem _ hxP 3)).mpr (by simpa using h3)
  have hrx1 : r * x * r⁻¹ * x⁻¹ ∈ K' :=
    (Subgroup.zpowers_le.mpr hxK) hrx
  have hrs1 : r * s * r⁻¹ * s⁻¹ ∈ K' := by
    rw [sym1119_comm_of_mem_zpowers hscl (sym1119_R_comm_c h r hrR)]; exact K'.one_mem
  have hRcomm' : ⁅Subgroup.closure ({r, x, s} : Set G), Subgroup.closure ({r, x, s} : Set G)⁆ ≤
      K' := by
    refine commutator_closure_le (T := ({r, x, s} : Set G)) (V := K') ?_ ?_
    · refine (Subgroup.closure_le _).mpr ?_
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with ht | ht | ht <;> rw [ht]
      · exact hK'norm r hrP
      · exact hK'norm x hxP
      · exact hK'norm s hsP
    · intro u hu v hv
      rw [commutatorElement_def]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rw [hu, hv]
      · exact sym1119_comm_self _ _
      · exact hrx1
      · exact hrs1
      · exact sym1119_comm_symm hrx1
      · exact sym1119_comm_self _ _
      · exact hxs1
      · exact sym1119_comm_symm hrs1
      · exact sym1119_comm_symm hxs1
      · exact sym1119_comm_self _ _
  have hRcomm : ⁅R, R⁆ ≤ K' := by rw [h.R_eq]; exact hRcomm'
  have hZ : ∀ z ∈ (sym1119W0 A x).subgroupOf (sec11P R g), ∀ p : sec11P R g,
      z * p * z⁻¹ * p⁻¹ ∈ K := by
    intro z hz p
    rw [Subgroup.mem_subgroupOf] at hz
    obtain ⟨i, u, hu, hze⟩ := (sym1119_mem_W0_iff h45 h).mp hz
    have hyK : ∀ n : ℤ, (x ^ 3) ^ n ∈ K' := fun n => K'.zpow_mem hxK n
    have hup := sym1119_comm_A_P h45 h113 h117 h hA2 hPA hu p.2
    have e : (z : G) * p * (z : G)⁻¹ * (p : G)⁻¹ =
        (x ^ 3) ^ i * (u * (p : G) * u⁻¹ * (p : G)⁻¹) *
          ((p : G) * ((x ^ 3) ^ i)⁻¹ * (p : G)⁻¹) := by
      rw [hze]; group
    have hpy : (p : G) * ((x ^ 3) ^ i)⁻¹ * (p : G)⁻¹ ∈ K' :=
      hK'n p p.2 _ (K'.inv_mem (hyK i))
    have h1 : (z : G) * p * (z : G)⁻¹ * (p : G)⁻¹ ∈ K' := by
      rw [e]
      exact K'.mul_mem (K'.mul_mem (hyK i) (hdzK' hup)) hpy
    have e1 : (⟨(z : G) * p * (z : G)⁻¹ * (p : G)⁻¹, (z * p * z⁻¹ * p⁻¹).2⟩ : sec11P R g) =
        z * p * z⁻¹ * p⁻¹ := Subtype.ext rfl
    have h2 := (hK'mem ((z : G) * p * (z : G)⁻¹ * (p : G)⁻¹) (z * p * z⁻¹ * p⁻¹).2).mp h1
    rwa [e1] at h2
  have hRR : ∀ u ∈ R.subgroupOf (sec11P R g), ∀ v ∈ R.subgroupOf (sec11P R g),
      u * v * u⁻¹ * v⁻¹ ∈ K := by
    intro u hu v hv
    rw [Subgroup.mem_subgroupOf] at hu hv
    have h1 : (u : G) * v * (u : G)⁻¹ * (v : G)⁻¹ ∈ K' := by
      have := hRcomm (Subgroup.commutator_mem_commutator hu hv)
      rwa [commutatorElement_def] at this
    have e1 : (⟨(u : G) * v * (u : G)⁻¹ * (v : G)⁻¹, (u * v * u⁻¹ * v⁻¹).2⟩ : sec11P R g) =
        u * v * u⁻¹ * v⁻¹ := Subtype.ext rfl
    have h2 := (hK'mem ((u : G) * v * (u : G)⁻¹ * (v : G)⁻¹) (u * v * u⁻¹ * v⁻¹).2).mp h1
    rwa [e1] at h2
  have hRgZ : ∀ u ∈ R.subgroupOf (sec11P R g),
      u * (⟨g, hgP⟩ : sec11P R g) * u⁻¹ * (⟨g, hgP⟩ : sec11P R g)⁻¹ ∈
        (sym1119W0 A x).subgroupOf (sec11P R g) := by
    intro u hu
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    have := hPP (Subgroup.commutator_mem_commutator u.2 hgP)
    rwa [commutatorElement_def] at this
  have hRg : R.subgroupOf (sec11P R g) ⊔ Subgroup.zpowers (⟨g, hgP⟩ : sec11P R g) = ⊤ := by
    apply Subgroup.map_injective (sec11P R g).subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (Item1119Proof.R_le_P R g),
      MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rfl
  have hRindex : (R.subgroupOf (sec11P R g)).index ≤ 3 :=
    Item1119Sym.relindex_le_three R g h.g_mem_normalizer hg3
  exact Item1119Sym.false_of_wreath_obstruction e (R.subgroupOf (sec11P R g)) ⟨g, hgP⟩ hRg
    hRindex hRR ((sym1119W0 A x).subgroupOf (sec11P R g)) hZ hRgZ


end Facts

end CFSG.RankThree.PartTwo.Sec11

end
