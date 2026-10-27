module

public import CFSG.Timmesfeld.Bridge.RootSetsConn1
public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.Timmesfeld.Bridge.RootSetsQuot

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  apply RootSubgroup.mem_normalizer_of_map_eq
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
      rintro _ ⟨x, hx, rfl⟩
      exact h x hx
    have hcard : Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    exact (Subgroup.eq_of_le_of_card_ge hle hcard.ge).ge

theorem exists_mem_normalizer_of_closure_ne [Finite G] {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p P) {S : Set G} (hSn : ∀ g ∈ P, ∀ s ∈ S, g * s * g⁻¹ ∈ S)
    (hgen : Subgroup.closure S = P) {T : Set G} (hT : T ⊆ S) (hne : Subgroup.closure T ≠ P) :
    ∃ y ∈ S, y ∉ Subgroup.closure T ∧
      y ∈ Subgroup.normalizer (Subgroup.closure T : Set G) := by
  classical
  set H := Subgroup.closure T with hH
  have hSP : S ⊆ P := fun s hs => hgen ▸ Subgroup.subset_closure hs
  have hHP : H ≤ P := by
    rw [← hgen]
    exact Subgroup.closure_mono hT
  let Q : Subgroup G → Prop := fun U =>
    H < U ∧ U ≤ P ∧ Subgroup.closure ((U : Set G) ∩ S) = U
  have hQP : Q P := by
    refine ⟨lt_of_le_of_ne hHP hne, le_rfl, ?_⟩
    rw [Set.inter_eq_right.2 hSP]
    exact hgen
  obtain ⟨U, -, hUmin⟩ := exists_minimal_le_of_wellFoundedLT Q P hQP
  obtain ⟨⟨hHU, hUP, hUgen⟩, hmin⟩ := hUmin
  have hUp : IsPGroup p U := hP.to_le hUP
  have : Group.IsNilpotent U := hUp.isNilpotent
  have hH'top : H.subgroupOf U ≠ ⊤ := by
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact lt_irrefl _ (lt_of_lt_of_le hHU h)
  obtain ⟨M, hMc, hHM⟩ := (eq_top_or_exists_le_coatom (H.subgroupOf U)).resolve_left hH'top
  have hMn : M.Normal :=
    ((Group.isNilpotent_of_finite_tfae (G := U)).out 1 3 rfl rfl).1 this M hMc
  set M' := M.map U.subtype with hM'
  have hHM' : H ≤ M' := by
    intro g hg
    refine ⟨⟨g, hHU.le hg⟩, ?_, rfl⟩
    apply hHM
    rw [Subgroup.mem_subgroupOf]
    exact hg
  have hM'U : M' ≤ U := Subgroup.map_subtype_le M
  have hM'neU : M' ≠ U := by
    intro h
    apply hMc.1
    rw [eq_top_iff]
    intro g _
    have : (g : G) ∈ M' := by
      rw [h]
      exact g.2
    obtain ⟨g', hg', hgg'⟩ := this
    rwa [Subtype.ext hgg'] at hg'
  set V := Subgroup.closure ((M' : Set G) ∩ S) with hV
  have hHV : H ≤ V := by
    rw [hH, Subgroup.closure_le]
    intro t ht
    exact Subgroup.subset_closure ⟨hHM' (Subgroup.subset_closure ht), hT ht⟩
  have hVM' : V ≤ M' := by
    rw [hV, Subgroup.closure_le]
    exact fun t ht => ht.1
  have hVH : V = H := by
    by_contra hVH
    have hQV : Q V := by
      refine ⟨lt_of_le_of_ne hHV (Ne.symm hVH), hVM'.trans (hM'U.trans hUP), ?_⟩
      apply le_antisymm
      · rw [Subgroup.closure_le]
        exact fun t ht => ht.1
      · rw [hV]
        exact Subgroup.closure_mono fun t ht => ⟨Subgroup.subset_closure ht, ht.2⟩
    have hUV := hmin hQV (hVM'.trans hM'U)
    exact hM'neU (le_antisymm hM'U (hUV.trans hVM'))
  have hnorm : ∀ g ∈ U, g ∈ Subgroup.normalizer (H : Set G) := by
    intro g hg
    apply mem_normalizer_of_conj_mem
    intro h hh
    rw [← hVH] at hh ⊢
    rw [hV] at hh ⊢
    induction hh using Subgroup.closure_induction with
    | mem t ht =>
      refine Subgroup.subset_closure ⟨?_, hSn g (hUP hg) t ht.2⟩
      obtain ⟨t', ht', rfl⟩ := ht.1
      have := hMn.conj_mem t' ht' ⟨g, hg⟩
      exact ⟨_, this, by simp⟩
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ hx
  obtain ⟨y, hyU, hyS, hyH⟩ : ∃ y ∈ U, y ∈ S ∧ y ∉ H := by
    by_contra hall
    push Not at hall
    have : U ≤ H := by
      rw [← hUgen, Subgroup.closure_le]
      exact fun t ht => hall t ht.1 ht.2
    exact lt_irrefl _ (lt_of_lt_of_le hHU this)
  exact ⟨y, hyS, hyH, hnorm y hyU⟩

namespace ConnCex

variable (hC : ConnCex D)
include hC

theorem not_special_of_le {K : Subgroup G} (hK : K ≠ ⊤) {a x : G} (ha : a ∈ D) (hx : x ∈ D)
    (haK : a ∈ K) (hxK : x ∈ K) (hax : ¬ Reach D a x) {d e : G} (hd : d ∈ D) (he : e ∈ D)
    (hdK : d ∈ K) (heK : e ∈ K) : orderOf (d * e) ≠ 4 := by
  intro h4
  have hle := hC.m2 K hK d hd e he h4 hdK heK
  have hda := reach_of_mem_compStab hC.setting.normal hC.setting.root hd ha (hle haK)
  have hdx := reach_of_mem_compStab hC.setting.normal hC.setting.root hd hx (hle hxK)
  exact hax (reach_trans (reach_symm hda) hdx)

theorem isOddTransp_of_le {K : Subgroup G} (hK : K ≠ ⊤) {a x : G} (ha : a ∈ D) (hx : x ∈ D)
    (haK : a ∈ K) (hxK : x ∈ K) (hax : ¬ Reach D a x) :
    Asc72.IsOddTransp {y | y ∈ D ∧ y ∈ K} := by
  have hD := hC.setting.root
  refine ⟨fun d hd => hD.orderOf_eq_two hd.1, fun d hd e he => ?_⟩
  rcases hD.orderOf_mul hd.1 he.1 with h | h | h
  · exact Or.inl (h ▸ dvd_rfl)
  · exact absurd h (hC.not_special_of_le hK ha hx haK hxK hax hd.1 he.1 hd.2 he.2)
  · exact Or.inr h

end ConnCex

structure ThirdKind (D : Set G) (a b c x z : G) : Prop where
  ha : a ∈ D
  hb : b ∈ D
  hc : c ∈ D
  hx : x ∈ D
  hab : a ≠ b
  hcab : Commute a b
  hca : Commute c a
  hcb : Commute c b
  hnD : a * b ∉ D
  hac : Reach D a c
  hax : ¬ Reach D a x
  hz : z = c * (a * b)
  hz1 : z ≠ 1
  hxz : Commute x z

namespace ThirdKind

variable {a b c x z : G}

theorem commute_a (h : ThirdKind D a b c x z) : Commute a z := by
  rw [h.hz]
  exact h.hca.symm.mul_right ((Commute.refl a).mul_right h.hcab)

theorem commute_b (h : ThirdKind D a b c x z) : Commute b z := by
  rw [h.hz]
  exact h.hcb.symm.mul_right (h.hcab.symm.mul_right (Commute.refl b))

theorem commute_c (h : ThirdKind D a b c x z) : Commute c z := by
  rw [h.hz]
  exact (Commute.refl c).mul_right (h.hca.mul_right h.hcb)

end ThirdKind

namespace ConnCex

variable (hC : ConnCex D)
include hC

theorem exists_thirdKind_config {a b : G} (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (hc : Commute a b) (hnD : a * b ∉ D) : ∃ c x z : G, ThirdKind D a b c x z := by
  have hD := hC.setting.root
  obtain ⟨x, hx, hax, n, hn, hord⟩ := hC.exists_thirdKind ha hb hab hc hnD
  obtain ⟨hcD, hac, hca, hcb⟩ := hC.thirdKind_commute ha hb hab hc hx hax hn hord
  have hu2 := hC.mul_mul_self_of_commute ha hb hc
  have hx2 := hD.mul_self_eq_one hx
  set r := x * (a * b) with hr
  have hxr : x * r * x⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, inv_eq_of_mul_eq_one_right hu2, hD.inv_eq hx, ← mul_assoc, hx2,
      one_mul]
  have hr2n : r ^ (2 * n) = 1 := by rw [← hord]; exact pow_orderOf_eq_one r
  have hz2 : r ^ n * r ^ n = 1 := by rw [← pow_add, ← two_mul, hr2n]
  have hxz : Commute x (r ^ n) := by
    have h1 : x * r ^ n * x⁻¹ = r ^ n := by
      rw [← conj_pow, hxr, inv_pow, inv_eq_of_mul_eq_one_right hz2]
    show x * r ^ n = r ^ n * x
    calc x * r ^ n = x * r ^ n * x⁻¹ * x := by group
      _ = r ^ n * x := by rw [h1]
  have hz1 : r ^ n ≠ 1 := by
    intro h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hdvd
    have := Nat.le_of_dvd hn.pos hdvd
    have := hn.pos
    omega
  refine ⟨r ^ n * (a * b), x, r ^ n, ha, hb, hcD, hx, hab, hc, hca, hcb, hnD, hac, hax, ?_,
    hz1, hxz⟩
  rw [mul_assoc, hu2, mul_one]

end ConnCex

namespace ThirdKind

variable {a b c x z : G}

theorem centralizer_ne_top (hC : ConnCex D) (h : ThirdKind D a b c x z) :
    Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
  intro htop
  have hzc : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer ({z} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  have := hC.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
  · rw [hb, Subgroup.mem_bot] at hzc
    exact h.hz1 hzc
  · have hax : x ∈ Subgroup.center G := ht ▸ Subgroup.mem_top x
    rw [Subgroup.mem_center_iff] at hax
    exact (opposite_of_not_reach hC.setting.root h.ha h.hx h.hax).1 (hax a)

theorem isOddTransp (hC : ConnCex D) (h : ThirdKind D a b c x z) :
    Asc72.IsOddTransp {y | y ∈ D ∧ y ∈ Subgroup.centralizer ({z} : Set G)} :=
  hC.isOddTransp_of_le (h.centralizer_ne_top hC) h.ha h.hx
    (Subgroup.mem_centralizer_singleton_iff.2 h.commute_a.eq)
    (Subgroup.mem_centralizer_singleton_iff.2 h.hxz.eq) h.hax

theorem exists_L (hC : ConnCex D) (h : ThirdKind D a b c x z) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ a ∈ P ∧ b ∈ P ∧ c ∈ P ∧
      P ≤ Subgroup.centralizer ({z} : Set G) ∧
      (∀ y ∈ D, (∀ l ∈ D, l ∈ P → Commute y l) → y ∈ P) ∧
      (∃ e ∈ D, ∃ f ∈ D, e ∈ P ∧ f ∈ P ∧ e ≠ f ∧ e * f ∈ D) ∧
      P = Subgroup.closure {y | y ∈ D ∧ y ∈ P} := by
  classical
  have := hC.setting.finite
  have hD := hC.setting.root
  have hN := hC.setting.normal
  let pr : Set G → Prop := fun A =>
    (∀ u ∈ A, u ∈ D ∧ Commute u z) ∧ ∀ u ∈ A, ∀ v ∈ A, Commute u v
  have h0 : pr {a, b, c} := by
    refine ⟨?_, ?_⟩
    · rintro u (rfl | rfl | rfl)
      · exact ⟨h.ha, h.commute_a⟩
      · exact ⟨h.hb, h.commute_b⟩
      · exact ⟨h.hc, h.commute_c⟩
    · rintro u (rfl | rfl | rfl) v (rfl | rfl | rfl)
      all_goals first
        | exact Commute.refl _
        | exact h.hcab
        | exact h.hcab.symm
        | exact h.hca
        | exact h.hca.symm
        | exact h.hcb
        | exact h.hcb.symm
  obtain ⟨L₀, hL₀, hmaxL⟩ := Finite.exists_le_maximal h0
  obtain ⟨hL₀D, hL₀c⟩ := hmaxL.1
  have hmem : ∀ y ∈ D, Commute y z → (∀ u ∈ L₀, Commute y u) → y ∈ L₀ := by
    intro y hy hyz hyL
    have hpr : pr (insert y L₀) := by
      refine ⟨?_, ?_⟩
      · rintro u (rfl | hu)
        · exact ⟨hy, hyz⟩
        · exact hL₀D u hu
      · rintro u (rfl | hu) v (rfl | hv)
        · exact Commute.refl _
        · exact hyL v hv
        · exact (hyL u hu).symm
        · exact hL₀c u hu v hv
    exact hmaxL.2 hpr (Set.subset_insert y L₀) (Set.mem_insert y L₀)
  set P := Subgroup.closure L₀ with hP
  have hP2 : IsPGroup 2 P := isPGroup_closure_of_pairwise
    (fun u hu v hv _ => hL₀c u hu v hv) (fun u hu => hD.mul_self_eq_one (hL₀D u hu).1)
  have haP : a ∈ P := Subgroup.subset_closure (hL₀ (by simp))
  have hbP : b ∈ P := Subgroup.subset_closure (hL₀ (by simp))
  have hcP : c ∈ P := Subgroup.subset_closure (hL₀ (by simp))
  have hPz : P ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hP, Subgroup.closure_le]
    exact fun u hu => Subgroup.mem_centralizer_singleton_iff.2 (hL₀D u hu).2.eq
  have hPc : ∀ g ∈ P, ∀ u ∈ L₀, Commute g u := by
    have hle : P ≤ Subgroup.centralizer L₀ := by
      rw [hP, Subgroup.closure_le]
      exact fun v hv => Subgroup.mem_centralizer_iff.2 fun w hw => (hL₀c w hw v hv).eq
    exact fun g hg u hu => (Subgroup.mem_centralizer_iff.1 (hle hg) u hu : Commute u g).symm
  have hDP : ∀ y ∈ D, y ∈ P → y ∈ L₀ := fun y hy hyP =>
    hmem y hy (Subgroup.mem_centralizer_singleton_iff.1 (hPz hyP)) (hPc y hyP)
  have hcent : ∀ y ∈ D, (∀ l ∈ D, l ∈ P → Commute y l) → y ∈ P := by
    intro y hy hyL
    have hyz : Commute y z := by
      rw [h.hz]
      exact (hyL c h.hc hcP).mul_right ((hyL a h.ha haP).mul_right (hyL b h.hb hbP))
    exact Subgroup.subset_closure (hmem y hy hyz fun u hu =>
      hyL u (hL₀D u hu).1 (Subgroup.subset_closure hu))
  have hPL : P = Subgroup.closure {y | y ∈ D ∧ y ∈ P} := by
    have hset : {y | y ∈ D ∧ y ∈ P} = L₀ := by
      ext y
      exact ⟨fun hy => hDP y hy.1 hy.2, fun hy => ⟨(hL₀D y hy).1, Subgroup.subset_closure hy⟩⟩
    rw [hset]
  refine ⟨P, hP2, haP, hbP, hcP, hPz, hcent, ?_, hPL⟩
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Sset : Set G := {y | y ∈ D ∧ y ∈ S} with hSset
  have hLS : L₀ ⊆ Sset := fun y hy => ⟨(hL₀D y hy).1, hPS (Subgroup.subset_closure hy)⟩
  have hS2 : IsPGroup 2 (Subgroup.closure Sset) :=
    S.isPGroup'.to_le (by rw [Subgroup.closure_le]; exact fun y hy => hy.2)
  have hne : Subgroup.closure L₀ ≠ Subgroup.closure Sset := by
    intro heq
    have hsub : Sset ⊆ L₀ := fun y hy =>
      hDP y hy.1 (by rw [hP, heq]; exact Subgroup.subset_closure hy)
    obtain ⟨d, hd, e, he, h4⟩ := hC.setting.nondeg
    have hde2 : IsPGroup 2 (Subgroup.closure ({d, e} : Set G)) := by
      refine isPGroup_two_closure_pair (hD.mul_self_eq_one hd) (hD.mul_self_eq_one he) (k := 2) ?_
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h4]
      exact pow_orderOf_eq_one _
    obtain ⟨S₁, hS₁⟩ := hde2.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₁ S
    have hmem' : ∀ t ∈ ({d, e} : Set G), g * t * g⁻¹ ∈ S := by
      intro t ht
      rw [← hg]
      exact Subgroup.smul_mem_pointwise_smul t (MulAut.conj g) _ (hS₁ (Subgroup.subset_closure ht))
    have hd' := hsub ⟨hN g d hd, hmem' d (by simp)⟩
    have he' := hsub ⟨hN g e he, hmem' e (by simp)⟩
    have hcomm := hL₀c _ hd' _ he'
    have hcomm' : Commute d e := (Commute.conj_iff g).1 (by simpa using hcomm)
    have : orderOf (d * e) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hcomm'.mul_pow, pow_two, pow_two, hD.mul_self_eq_one hd, hD.mul_self_eq_one he,
        one_mul]
    rw [h4] at this
    exact absurd this (by decide)
  obtain ⟨y, hyS, hyL, hyN⟩ := exists_mem_normalizer_of_closure_ne hS2
    (fun g hg s hs => by
      have hgS : g ∈ S := (Subgroup.closure_le (S : Subgroup G)).2 (fun t ht => ht.2) hg
      exact ⟨hN g s hs.1, S.mul_mem (S.mul_mem hgS hs.2) (S.inv_mem hgS)⟩)
    rfl hLS hne
  have hyD := hyS.1
  obtain ⟨e, he, hye⟩ : ∃ e ∈ L₀, ¬ Commute y e := by
    by_contra hall
    push Not at hall
    exact hyL (hcent y hyD fun l hl hlP => hall l (hDP l hl hlP))
  set f := y * e * y⁻¹ with hf
  have hfL : f ∈ L₀ := hDP f (hN y e (hL₀D e he).1)
    ((Subgroup.mem_normalizer_iff.1 hyN e).1 (Subgroup.subset_closure he))
  have hef : e ≠ f := by
    intro heq
    apply hye
    show y * e = e * y
    calc y * e = y * e * y⁻¹ * y := by group
      _ = e * y := by rw [← hf, ← heq]
  have hye4 : orderOf (y * e) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hyD (hL₀D e he).1 with h' | h' | ⟨hodd, -⟩
    · exact absurd h' hye
    · exact h'
    · exfalso
      obtain ⟨k, hk⟩ := S.isPGroup' ⟨y * e, S.mul_mem hyS.2 (hLS he).2⟩
      have hk' : (y * e) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h1 : orderOf (y * e) = 1 := by
        have hdvd := orderOf_dvd_of_pow_eq_one hk'
        rcases (Nat.dvd_prime_pow Nat.prime_two).1 hdvd with ⟨j, -, hj⟩
        rcases j with _ | j
        · simpa using hj
        · rw [hj] at hodd
          exact absurd hodd (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero j⟩))
      rw [orderOf_eq_one_iff, mul_eq_one_iff_eq_inv, hD.inv_eq (hL₀D e he).1] at h1
      exact hye (by rw [h1])
  have hfe : f * e ∈ D := by
    have := hD.sq_mem hyD (hL₀D e he).1 hye4
    rwa [pow_two, show y * e * (y * e) = y * e * y⁻¹ * e by rw [hD.inv_eq hyD]; group] at this
  have hcef : Commute e f := hL₀c e he f hfL
  exact ⟨e, (hL₀D e he).1, f, (hL₀D f hfL).1, Subgroup.subset_closure he,
    Subgroup.subset_closure hfL, hef, hcef.eq ▸ hfe⟩

end ThirdKind

structure Step6 (D : Set G) (a b c x z : G) (P : Subgroup G) : Prop
    extends ThirdKind D a b c x z where
  hP2 : IsPGroup 2 P
  haP : a ∈ P
  hbP : b ∈ P
  hcP : c ∈ P
  hPz : P ≤ Subgroup.centralizer ({z} : Set G)
  hcent : ∀ y ∈ D, (∀ l ∈ D, l ∈ P → Commute y l) → y ∈ P
  hLL : ∃ e ∈ D, ∃ f ∈ D, e ∈ P ∧ f ∈ P ∧ e ≠ f ∧ e * f ∈ D
  hPL : P = Subgroup.closure {y | y ∈ D ∧ y ∈ P}

@[expose] def lsub (D : Set G) (x : G) (P : Subgroup G) : Subgroup G :=
  Subgroup.closure (insert x {y | y ∈ D ∧ y ∈ P})

namespace ConnCex

variable (hC : ConnCex D)
include hC

theorem exists_step6 {a b : G} (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b) (hc : Commute a b)
    (hnD : a * b ∉ D) : ∃ c x z : G, ∃ P : Subgroup G, Step6 D a b c x z P := by
  obtain ⟨c, x, z, h⟩ := hC.exists_thirdKind_config ha hb hab hc hnD
  obtain ⟨P, hP2, haP, hbP, hcP, hPz, hcent, hLL, hPL⟩ := h.exists_L hC
  exact ⟨c, x, z, P, { h with hP2, haP, hbP, hcP, hPz, hcent, hLL, hPL }⟩

end ConnCex

namespace Step6

variable {a b c x z : G} {P : Subgroup G}

theorem mem_lsub_x : x ∈ lsub D x P := Subgroup.subset_closure (Set.mem_insert x _)

theorem mem_lsub_of_mem {y : G} (hy : y ∈ D) (hyP : y ∈ P) : y ∈ lsub D x P :=
  Subgroup.subset_closure (Set.mem_insert_of_mem x ⟨hy, hyP⟩)

theorem lsub_le_centralizer (h : Step6 D a b c x z P) :
    lsub D x P ≤ Subgroup.centralizer ({z} : Set G) := by
  rw [lsub, Subgroup.closure_le]
  rintro y (rfl | hy)
  · exact Subgroup.mem_centralizer_singleton_iff.2 h.hxz.eq
  · exact h.hPz hy.2

theorem commute_of_mem (hC : ConnCex D) (h : Step6 D a b c x z P) {u v : G} (hu : u ∈ D)
    (hv : v ∈ D) (huP : u ∈ P) (hvP : v ∈ P) : Commute u v :=
  (h.isOddTransp hC).commute_of_isPGroup h.hP2 ⟨hu, h.hPz huP⟩ ⟨hv, h.hPz hvP⟩ huP hvP

theorem reach_of_mem (hC : ConnCex D) (h : Step6 D a b c x z P) {u : G} (hu : u ∈ D)
    (huP : u ∈ P) : Reach D a u :=
  reach_of_commute h.ha hu (h.commute_of_mem hC h.ha hu h.haP huP)

theorem mem_classIn (hC : ConnCex D) (h : Step6 D a b c x z P) {u : G} (hu : u ∈ D)
    (huP : u ∈ P) : u ∈ classIn (lsub D x P) x := by
  have hux : ¬ Reach D u x := fun hr => h.hax (reach_trans (h.reach_of_mem hC hu huP) hr)
  obtain ⟨-, hodd⟩ := opposite_of_not_reach hC.setting.root hu h.hx hux
  have hodd' : Odd (orderOf (x * u)) := by
    rw [show x * u = (u * x)⁻¹ by
      rw [mul_inv_rev, hC.setting.root.inv_eq hu, hC.setting.root.inv_eq h.hx], orderOf_inv]
    exact hodd
  exact mem_classIn_of_odd hC.setting.root h.hx hu mem_lsub_x (mem_lsub_of_mem hu huP) hodd'

theorem closure_classIn (hC : ConnCex D) (h : Step6 D a b c x z P) :
    Subgroup.closure (classIn (lsub D x P) x) = lsub D x P := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact classIn_subset _ mem_lsub_x
  · rw [lsub, Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact Subgroup.subset_closure (mem_classIn_self _ y)
    · exact Subgroup.subset_closure (h.mem_classIn hC hy.1 hy.2)

theorem isOddTransp_classIn (hC : ConnCex D) (h : Step6 D a b c x z P) :
    Asc72.IsOddTransp (classIn (lsub D x P) x) :=
  (h.isOddTransp hC).mono fun _ hy =>
    ⟨classIn_subset_of_normal hC.setting.normal _ h.hx hy,
      h.lsub_le_centralizer (classIn_subset _ mem_lsub_x hy)⟩

end Step6

end CFSG.Timmesfeld.Bridge
