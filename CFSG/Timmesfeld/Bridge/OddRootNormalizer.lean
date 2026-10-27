module

public import CFSG.Timmesfeld.Bridge.OddRootLocalQ

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem closure_prod_le_Qof (D : Set G) (d x : G) :
    Subgroup.closure {g : G | ∃ a ∈ rootSet D d, ∃ b ∈ rootSet D d,
      a ≠ b ∧ a * b ∈ Qof D d x ∧ g = a * b} ≤ Qof D d x := by
  rw [Subgroup.closure_le]
  rintro g ⟨a, ha, b, hb, -, hQ, rfl⟩
  exact hQ

private theorem closure_prod_le_rootGroup (D : Set G) (d x : G) :
    Subgroup.closure {g : G | ∃ a ∈ rootSet D d, ∃ b ∈ rootSet D d,
      a ≠ b ∧ a * b ∈ Qof D d x ∧ g = a * b} ≤ rootGroup D d := by
  rw [Subgroup.closure_le]
  rintro g ⟨a, ha, b, hb, -, -, rfl⟩
  exact (rootGroup D d).mul_mem (rootSet_subset_rootGroup D d ha)
    (rootSet_subset_rootGroup D d hb)

private theorem sylow_le_normalizer_closure_prod {d x : G} (hd : d ∈ D)
    {C S : Subgroup G} (hC : GoodCompl D d x C S) :
    S ≤ Subgroup.normalizer (Subgroup.closure {g : G | ∃ a ∈ rootSet D d,
      ∃ b ∈ rootSet D d, a ≠ b ∧ a * b ∈ Qof D d x ∧ g = a * b} : Set G) := by
  intro s hs
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hF : Subgroup.closure {g : G | ∃ a ∈ rootSet D d, ∃ b ∈ rootSet D d,
      a ≠ b ∧ a * b ∈ Qof D d x ∧ g = a * b} ≤ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.closure_le]
    rintro g ⟨a, ha, b, hb, -, -, rfl⟩
    by_cases hs1 : s = 1
    · subst hs1
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      simp
    · have hsE : s ∈ rootSet D d := hC.S_root s hs hs1
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((commute_of_mem_rootSet hd ha hsE).mul_left
          (commute_of_mem_rootSet hd hb hsE)).eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hF hf))

private theorem rootSet_subset_closure_prod_sup
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D)
    (hdx : ¬ Commute d x) (hpx : PSL2Pair D d x) {C S : Subgroup G}
    (hC : GoodCompl D d x C S) :
    rootSet D d ⊆ (((Subgroup.closure {g : G | ∃ a ∈ rootSet D d, ∃ b ∈ rootSet D d,
      a ≠ b ∧ a * b ∈ Qof D d x ∧ g = a * b} : Subgroup G) ⊔ S : Subgroup G) : Set G) := by
  intro e he
  obtain ⟨w, hw, s, hs, heq⟩ := rootSet_subset_Wof_mul_sylow h hd hx hdx hpx hC he
  have heq' : w * s = e := heq
  rw [← heq']
  change w * s ∈ (((Subgroup.closure {g : G | ∃ a ∈ rootSet D d, ∃ b ∈ rootSet D d,
      a ≠ b ∧ a * b ∈ Qof D d x ∧ g = a * b} : Subgroup G) ⊔ S : Subgroup G) : Set G)
  by_cases hw1 : w = 1
  · rw [hw1, one_mul]
    exact Subgroup.mem_sup_right hs
  · have hs1 : s ≠ 1 := by
      intro hs1'
      have heQ : e ∈ Qof D d x := by
        rw [← heq']
        change w * s ∈ Qof D d x
        rw [hs1', mul_one]
        exact hw.2
      exact not_mem_Qof_of_mem_rootSet h.setup.oddT hx hdx he heQ
    have hsE : s ∈ rootSet D d := hC.S_root s hs hs1
    have hsi : s⁻¹ = s := h.setup.oddT.inv_eq hsE.1
    have hsinvE : s⁻¹ ∈ rootSet D d := by rw [hsi]; exact hsE
    have hw_eq : w = e * s⁻¹ := by
      rw [← heq']
      group
    have hne : e ≠ s⁻¹ := by
      intro hEq
      apply hw1
      rw [hw_eq, hEq, hsi]
      exact h.setup.oddT.mul_self_eq_one hsE.1
    have hQ : e * s⁻¹ ∈ Qof D d x := by
      rw [← hw_eq]
      exact hw.2
    have hwF : w ∈ Subgroup.closure {g : G | ∃ a ∈ rootSet D d, ∃ b ∈ rootSet D d,
        a ≠ b ∧ a * b ∈ Qof D d x ∧ g = a * b} :=
      Subgroup.subset_closure ⟨e, he, s⁻¹, hsinvE, hne, hQ, hw_eq⟩
    exact Subgroup.mul_mem_sup hwF hs

theorem Wof_eq_closure
    {G : Type} [Group G] [Finite G] {D : Set G} (h : Hyp G D)
    {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x) (hpx : PSL2Pair D d x) :
    Wof D d x = Subgroup.closure
      {g | ∃ a ∈ rootSet D d, ∃ b ∈ rootSet D d, a ≠ b ∧ a * b ∈ Qof D d x ∧ g = a * b} := by
  let F : Subgroup G := Subgroup.closure {g : G | ∃ a ∈ rootSet D d, ∃ b ∈ rootSet D d,
    a ≠ b ∧ a * b ∈ Qof D d x ∧ g = a * b}
  have hFQ : F ≤ Qof D d x := closure_prod_le_Qof D d x
  have hFE : F ≤ rootGroup D d := closure_prod_le_rootGroup D d x
  have hFW : F ≤ Wof D d x := le_inf hFE hFQ
  obtain ⟨C, S, hC⟩ := exists_goodCompl h hd hx hdx hpx
  have hrootsub : rootSet D d ⊆ ((F ⊔ S : Subgroup G) : Set G) :=
    rootSet_subset_closure_prod_sup h hd hx hdx hpx hC
  have hE : rootGroup D d ≤ F ⊔ S := by
    rw [rootGroup, Subgroup.closure_le]
    exact hrootsub
  have hSnorm : S ≤ Subgroup.normalizer (F : Set G) :=
    sylow_le_normalizer_closure_prod hd hC
  have hFS : ((F ⊔ S : Subgroup G) : Set G) = (F : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left F S hSnorm
  have hSbot : S ⊓ Qof D d x = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    have hmem : s ∈ C ⊓ Qof D d x := ⟨hC.S_le hs.1, hs.2⟩
    rw [hC.inf] at hmem
    exact hmem
  apply le_antisymm ?_ hFW
  intro w hw
  have hwSup : w ∈ ((F ⊔ S : Subgroup G) : Set G) := hE hw.1
  have hwProd : w ∈ (F : Set G) * (S : Set G) := by rwa [hFS] at hwSup
  obtain ⟨f, hf, s, hs, hfs⟩ := Set.mem_mul.mp hwProd
  have hsQ : s ∈ Qof D d x := by
    have hseq : s = f⁻¹ * w := by rw [← hfs]; group
    rw [hseq]
    exact (Qof D d x).mul_mem ((Qof D d x).inv_mem (hFQ hf)) hw.2
  have hsbot : s ∈ S ⊓ Qof D d x := ⟨hs, hsQ⟩
  rw [hSbot] at hsbot
  have hs1 : s = 1 := Subgroup.mem_bot.mp hsbot
  rw [← hfs, hs1, mul_one]
  exact hf

private theorem compl_inf_normalizer_sylow_le_normalizer_rootSet (h : Hyp G D) {d x : G}
    (hx : x ∈ D) {C S : Subgroup G} (hC : GoodCompl D d x C S) :
    C ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (rootSet D d) := by
  intro b hb
  obtain ⟨hbC, hbN⟩ := hb
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hx2 : x * x = 1 := h.setup.oddT.mul_self_eq_one hx
    have hEq : Subgroup.zpowers x = S := by
      refine hC.S_sylow (Subgroup.zpowers x) ?_ ?_ ?_
      · rw [hbot]; exact bot_le
      · intro g hg
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        exact Subgroup.zpow_mem C hC.x_mem k
      · exact isPGroup_two_zpowers_of_mul_self_eq_one hx2
    have hxS : x ∈ S := by rw [← hEq]; exact Subgroup.mem_zpowers x
    exact h.setup.oddT.ne_one hx (by rw [hbot] at hxS; exact Subgroup.mem_bot.mp hxS)
  haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hSne
  obtain ⟨s, hs1⟩ := exists_ne (1 : ↥S)
  have hsS : (s : G) ∈ S := s.2
  have hs1' : (s : G) ≠ 1 := fun h1 => hs1 (Subtype.ext h1)
  have hsE : (s : G) ∈ rootSet D d := hC.S_root _ hsS hs1'
  have hbsS : b * (s : G) * b⁻¹ ∈ S :=
    (Subgroup.mem_set_normalizer_iff.mp hbN (s : G)).mp hsS
  have hbs1 : b * (s : G) * b⁻¹ ≠ 1 := by
    intro h1
    apply hs1'
    have h2 := congrArg (fun z => b⁻¹ * z * b) h1
    simpa [mul_assoc] using h2
  have hbsE : b * (s : G) * b⁻¹ ∈ rootSet D d := hC.S_root _ hbsS hbs1
  have hconj : rootSet D (b * (s : G) * b⁻¹) =
      (fun z => b * z * b⁻¹) '' rootSet D (s : G) :=
    rootSet_conj h.setup.isClass b (s : G)
  have hEs : rootSet D (s : G) = rootSet D d := rootSet_eq_of_mem hsE
  have himg : (fun z => b * z * b⁻¹) '' rootSet D d = rootSet D d := by
    rw [← hEs, ← hconj]
    exact (rootSet_eq_of_mem hbsE).trans hEs.symm
  rw [Subgroup.mem_set_normalizer_iff]
  intro e
  constructor
  · intro he
    have : b * e * b⁻¹ ∈ (fun z => b * z * b⁻¹) '' rootSet D d := ⟨e, he, rfl⟩
    rwa [himg] at this
  · intro he
    have : b * e * b⁻¹ ∈ (fun z => b * z * b⁻¹) '' rootSet D d := by rwa [himg]
    obtain ⟨e0, he0, h0⟩ := this
    have hee : e0 = e := by
      have h2 := congrArg (fun z => b⁻¹ * z * b) h0
      simpa [mul_assoc] using h2
    rwa [hee] at he0

private theorem compl_inf_normalizer_sylow_le_normalizer_rootGroup (h : Hyp G D) {d x : G}
    (hx : x ∈ D) {C S : Subgroup G} (hC : GoodCompl D d x C S) :
    C ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (rootGroup D d) := by
  intro b hb
  have hbE := compl_inf_normalizer_sylow_le_normalizer_rootSet h hx hC hb
  have himg : (fun z => b * z * b⁻¹) '' rootSet D d = rootSet D d := by
    ext e
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (Subgroup.mem_set_normalizer_iff.mp hbE z).mp hz
    · intro he
      refine ⟨b⁻¹ * e * b, ?_, by group⟩
      exact (Subgroup.mem_set_normalizer_iff.mp hbE (b⁻¹ * e * b)).mpr
        (by simpa [mul_assoc] using he)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [rootGroup, MonoidHom.map_closure]
  change Subgroup.closure ((fun z => b * z * b⁻¹) '' rootSet D d) =
    Subgroup.closure (rootSet D d)
  rw [himg]

private theorem compl_inf_normalizer_sylow_le_normalizer_Qof {d x : G} {C S : Subgroup G}
    (hC : GoodCompl D d x C S) :
    C ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (Qof D d x) := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb q hq
  exact conj_mem_Qof d x (hC.le hb.1) hq

private theorem compl_inf_normalizer_sylow_le_normalizer_Wof (h : Hyp G D) {d x : G}
    (hx : x ∈ D) {C S : Subgroup G} (hC : GoodCompl D d x C S) :
    C ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (Wof D d x) := by
  intro b hb
  have hbE := compl_inf_normalizer_sylow_le_normalizer_rootGroup h hx hC hb
  have hbQ := compl_inf_normalizer_sylow_le_normalizer_Qof hC hb
  rw [Subgroup.mem_normalizer_iff] at hbE hbQ ⊢
  intro w
  constructor
  · intro hw
    rw [Wof] at hw ⊢
    rw [Subgroup.mem_inf] at hw ⊢
    exact ⟨(hbE w).mp hw.1, (hbQ w).mp hw.2⟩
  · intro hw
    rw [Wof] at hw ⊢
    rw [Subgroup.mem_inf] at hw ⊢
    exact ⟨(hbE w).mpr hw.1, (hbQ w).mpr hw.2⟩

private theorem conj_prod_mem_normalizer (h : Hyp G D) {d x : G} (hd : d ∈ D) {t a b : G}
    (htD : t ∈ D) (htX : t ∈ rootGen D d x) (ht2 : t * t = 1) (ha : a ∈ rootSet D d)
    (hb : b ∈ rootSet D d) (hab : a ≠ b) (hQ : a * b ∈ Qof D d x) :
    t * (a * b) * t⁻¹ ∈ Subgroup.normalizer (rootSet D d) := by
  set w : G := a * b with hwdef
  have hw2 : w * w = 1 := by
    rw [hwdef]
    have hcomm : Commute a b := commute_of_mem_rootSet hd ha hb
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hcomm.eq]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [h.setup.oddT.mul_self_eq_one ha.1,
            h.setup.oddT.mul_self_eq_one hb.1, mul_one]
  have hwQ : w ∈ Qof D d x := by rw [hwdef]; exact hQ
  have hconjQ : t * w * t⁻¹ ∈ Qof D d x := conj_mem_Qof d x htX hwQ
  have hsq : (w * t) * (w * t) ∈ Qof D d x := by
    have e : (w * t) * (w * t) = w * (t * w * t⁻¹) * (t * t) := by group
    rw [e, ht2, mul_one]
    exact (Qof D d x).mul_mem hwQ hconjQ
  obtain ⟨k, hk⟩ := isPGroup_Qof d x ⟨_, hsq⟩
  have h2 : ∃ k : ℕ, (w * t) ^ 2 ^ k = 1 := by
    refine ⟨k + 1, ?_⟩
    have hk' : ((w * t) ^ 2) ^ 2 ^ k = 1 := by
      simpa [pow_two] using congrArg Subtype.val hk
    rw [show 2 ^ (k + 1) = 2 * 2 ^ k by rw [pow_succ]; ring, pow_mul]
    exact hk'
  have hwtD : w * t * w⁻¹ ∈ D := h.setup.normal w t htD
  have hcomm : Commute w (t * w * t⁻¹) :=
    commute_conj_of_two_pow h.setup.oddT hw2 htD hwtD h2
  have hmem : t * w * t⁻¹ ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hle := centralizer_mul_le_normalizer h.setup.oddT h.setup.normal hd ha hb hab
  have := hle hmem
  simpa [hwdef] using this

private theorem conj_Wof_le_normalizer
    (h : Hyp G D) {d x t : G} (hd : d ∈ D) (hx : x ∈ D)
    (hdx : ¬ Commute d x) (hpx : PSL2Pair D d x) (htD : t ∈ D)
    (htX : t ∈ rootGen D d x) (ht2 : t * t = 1) :
    conjSubgroup t (Wof D d x) ≤ Subgroup.normalizer (rootSet D d) := by
  rw [Wof_eq_closure h hd hx hdx hpx]
  rw [conjSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
  rintro g ⟨f, hf, rfl⟩
  obtain ⟨a, ha, b, hb, hab, hQ, rfl⟩ := hf
  simpa [MulAut.conj_apply, mul_assoc] using
    conj_prod_mem_normalizer h hd htD htX ht2 ha hb hab hQ

theorem GoodCompl.exists_sylow_map_eq (h : Hyp G D) {d x : G} {C S : Subgroup G}
    (hC : GoodCompl D d x C S) :
    ∃ SC : Sylow 2 ↥C, Subgroup.map C.subtype (SC : Subgroup ↥C) = S := by
  have hS2 : IsPGroup 2 S := hC.toIsRootCompl.isPGroup h
  let SC : Sylow 2 ↥C :=
    { toSubgroup := S.subgroupOf C
      isPGroup' := hS2.comap_of_injective C.subtype C.subtype_injective
      is_maximal' := fun {H} hH hle => by
        have hmap2 : IsPGroup 2 (Subgroup.map C.subtype H) := hH.map C.subtype
        have hSle : S ≤ Subgroup.map C.subtype H := by
          intro s hs
          have hmem : (⟨s, hC.S_le hs⟩ : ↥C) ∈ S.subgroupOf C := by
            show s ∈ S
            exact hs
          exact Subgroup.mem_map_of_mem C.subtype (hle hmem)
        have hEq : Subgroup.map C.subtype H = S :=
          hC.S_sylow _ hSle (Subgroup.map_subtype_le H) hmap2
        rw [← Subgroup.comap_map_eq_self_of_injective C.subtype_injective H, hEq,
          Subgroup.comap_subtype] }
  refine ⟨SC, ?_⟩
  rw [show (SC : Subgroup ↥C) = S.subgroupOf C from rfl,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hC.S_le]

private theorem exists_distinct_sylow_compl (h : Hyp G D) {d x : G} (hpx : PSL2Pair D d x)
    {C S : Subgroup G} (hC : GoodCompl D d x C S) {g : G} (hg : g ∈ C)
    (hgS : conjSubgroup g S ≠ S) :
    ∃ (SC SCg : Sylow 2 ↥C) (n : ℕ) (eC : ↥C ≃* PSL2Model n),
      2 ≤ n ∧ SC ≠ SCg ∧
        Subgroup.map C.subtype (SC : Subgroup ↥C) = S ∧
        Subgroup.map C.subtype (SCg : Subgroup ↥C) = conjSubgroup g S := by
  obtain ⟨n, hn, ⟨eC⟩⟩ := exists_mulEquiv_PSL2Model_of_compl hpx hC.le hC.inf hC.sup
  obtain ⟨SC, hmapSC⟩ := hC.exists_sylow_map_eq h
  let gC : ↥C := ⟨g, hg⟩
  let SCg : Sylow 2 ↥C := Sylow.mapSurjective (f := (MulAut.conj gC).toMonoidHom)
    (MulAut.conj gC).surjective SC
  have hmapSCg : Subgroup.map C.subtype (SCg : Subgroup ↥C) = conjSubgroup g S := by
    have hcoe : (SCg : Subgroup ↥C) =
        Subgroup.map (MulAut.conj gC).toMonoidHom (SC : Subgroup ↥C) :=
      Sylow.coe_mapSurjective (f := (MulAut.conj gC).toMonoidHom)
        (MulAut.conj gC).surjective SC
    rw [hcoe, Subgroup.map_map]
    have hcomp : C.subtype.comp (MulAut.conj gC).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp C.subtype := by
      ext z
      rfl
    rw [hcomp, ← Subgroup.map_map, hmapSC]
    rfl
  have hne : SC ≠ SCg := by
    intro hEq
    apply hgS
    have h := congrArg (fun P : Sylow 2 ↥C =>
      Subgroup.map C.subtype (P : Subgroup ↥C)) hEq
    rw [hmapSC, hmapSCg] at h
    exact h.symm
  exact ⟨SC, SCg, n, eC, hn, hne, hmapSC, hmapSCg⟩

private theorem exists_swap_involution_compl (h : Hyp G D) {d x : G} (hx : x ∈ D)
    (hpx : PSL2Pair D d x) {C S : Subgroup G} (hC : GoodCompl D d x C S) {g : G}
    (hg : g ∈ C) (hgS : conjSubgroup g S ≠ S) :
    ∃ t : G, t ∈ C ∧ t ∈ D ∧ t ∈ rootGen D d x ∧ t * t = 1 ∧
      conjSubgroup t S = conjSubgroup g S := by
  obtain ⟨SC, SCg, n, eC, hn, hne, hmapSC, hmapSCg⟩ :=
    exists_distinct_sylow_compl h hpx hC hg hgS
  obtain ⟨tC, htC2, htC1, htCconj⟩ := psl2_exists_involution_swap eC hn hne
  have htGconj : conjSubgroup (tC : G) S = conjSubgroup g S := by
    have h := congrArg (fun H : Subgroup ↥C => Subgroup.map C.subtype H) htCconj
    have hl : Subgroup.map C.subtype (conjSubgroup tC (SC : Subgroup ↥C)) =
        conjSubgroup (tC : G) S := by
      rw [conjSubgroup, Subgroup.map_map]
      have hcomp : C.subtype.comp (MulAut.conj tC).toMonoidHom =
          (MulAut.conj (tC : G)).toMonoidHom.comp C.subtype := by
        ext z
        rfl
      rw [hcomp, ← Subgroup.map_map, hmapSC]
      rfl
    rw [hl, hmapSCg] at h
    exact h
  have htD : (tC : G) ∈ D :=
    involution_mem_D_of_psl2 h hn eC hC.x_mem hx tC.2
      (by simpa using congrArg Subtype.val htC2)
      (fun h1 => htC1 (Subtype.ext h1))
  have htX : (tC : G) ∈ rootGen D d x := hC.le tC.2
  exact ⟨(tC : G), tC.2, htD, htX, by simpa using congrArg Subtype.val htC2,
    htGconj⟩

private theorem compl_conj_Wof_le_normalizer
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D)
    (hdx : ¬ Commute d x) (hpx : PSL2Pair D d x) {C S : Subgroup G}
    (hC : GoodCompl D d x C S) {g : G} (hg : g ∈ C) :
    conjSubgroup g (Wof D d x) ≤ Subgroup.normalizer (rootSet D d) := by
  have hBnormW := compl_inf_normalizer_sylow_le_normalizer_Wof h hx hC
  by_cases hgS : conjSubgroup g S = S
  · have hgN : g ∈ Subgroup.normalizer (S : Set G) :=
      mem_normalizer_iff_conjSubgroup_eq.mpr hgS
    have hgB : g ∈ C ⊓ Subgroup.normalizer (S : Set G) := ⟨hg, hgN⟩
    have hW : conjSubgroup g (Wof D d x) = Wof D d x :=
      mem_normalizer_iff_conjSubgroup_eq.mp (hBnormW hgB)
    rw [hW]
    exact (Wof_le_rootGroup d x).trans (rootGroup_le_normalizer h.setup.normal d)
  · obtain ⟨t, htC, htD, htX, ht2, htconj⟩ :=
      exists_swap_involution_compl h hx hpx hC hg hgS
    have hconjW := conj_Wof_le_normalizer h hd hx hdx hpx htD htX ht2
    let hh : G := g⁻¹ * t
    have hhC : hh ∈ C := C.mul_mem (C.inv_mem hg) htC
    have hhS : conjSubgroup hh S = S := by
      rw [show hh = g⁻¹ * t from rfl, ← conjSubgroup_conjSubgroup, htconj,
        conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    have hhN : hh ∈ Subgroup.normalizer (S : Set G) :=
      mem_normalizer_iff_conjSubgroup_eq.mpr hhS
    have hhB : hh ∈ C ⊓ Subgroup.normalizer (S : Set G) := ⟨hhC, hhN⟩
    have hhW : conjSubgroup hh (Wof D d x) = Wof D d x :=
      mem_normalizer_iff_conjSubgroup_eq.mp (hBnormW hhB)
    have hEqConj : conjSubgroup t (Wof D d x) = conjSubgroup g (Wof D d x) := by
      rw [show t = g * hh from by
        rw [show hh = g⁻¹ * t from rfl]; group,
        ← conjSubgroup_conjSubgroup, hhW]
    rw [hEqConj] at hconjW
    exact hconjW

theorem Qof_le_normalizer
    {G : Type} [Group G] [Finite G] {D : Set G} (h : Hyp G D)
    {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x) (hpx : PSL2Pair D d x) :
    Qof D d x ≤ Subgroup.normalizer (rootSet D d) := by
  obtain ⟨C, S, hC⟩ := exists_goodCompl h hd hx hdx hpx
  rw [Qof_eq_closure h hd hx hdx hpx hC, Subgroup.closure_le]
  rintro g ⟨c, hc, w, hw, rfl⟩
  exact (compl_conj_Wof_le_normalizer h hd hx hdx hpx hC hc)
    (conj_mem_conjSubgroup c hw)

end CFSG.Timmesfeld.Bridge.OddRoot
