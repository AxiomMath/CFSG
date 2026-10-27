module

public import CFSG.RankThree.GF2n.Tim79aSec23NoSq
public import CFSG.Timmesfeld.Transvection.QTwoThin

public section
namespace CFSG.OddTranspositions
open CFSG.Timmesfeld CFSG.Blueprint.Fischer

theorem eq_one_or_eq_swap_of_eq_on_compl {m : ℕ} {a b : Fin m}
    (hab : a ≠ b) {g : Equiv.Perm (Fin m)}
    (h : ∀ y : Fin m, y ≠ a → y ≠ b → g y = y) :
    g = 1 ∨ g = Equiv.swap a b := by
  have hga : g a = a ∨ g a = b := by
    by_cases hga : g a = a
    · exact Or.inl hga
    · right
      by_contra hgb
      have hmem := h (g a) hga hgb
      exact hga (g.injective hmem)
  rcases hga with hga | hga
  · left
    have hgb : g b = b := by
      by_contra hgb
      have hne : g b ≠ a := by
        intro hba
        exact hab (g.injective (by rw [hba, hga]))
      have hmem := h (g b) hne hgb
      exact hgb (g.injective hmem)
    exact Equiv.ext fun y => by
      by_cases hya : y = a
      · subst y; exact hga
      · by_cases hyb : y = b
        · subst y; exact hgb
        · simpa using h y hya hyb
  · right
    have hgb : g b = a := by
      by_contra hgb
      have hne : g b ≠ b := by
        intro hbb
        exact hab (g.injective (by rw [hbb, hga]))
      have hmem := h (g b) hgb hne
      exact hne (g.injective hmem)
    exact Equiv.ext fun y => by
      by_cases hya : y = a
      · subst y; simpa using hga
      · by_cases hyb : y = b
        · subst y; simpa using hgb
        · rw [h y hya hyb]
          exact (Equiv.swap_apply_of_ne_of_ne hya hyb).symm

theorem pCore_two_perm_eq_bot_of_three_or_five_le {k : ℕ} (hk : k = 3 ∨ 5 ≤ k) :
    CFSG.pCore 2 (Equiv.Perm (Fin k)) = ⊥ := by
  rcases hk with rfl | hk
  ·
    have key : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 →
        ∃ τ : Equiv.Perm (Fin 3),
          σ * (τ * σ * τ⁻¹) ≠ 1 ∧ (σ * (τ * σ * τ⁻¹)) ^ 3 = 1 := by
      decide +kernel
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    by_contra hne
    obtain ⟨τ, h1, h3⟩ := key σ (by simpa using hne)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnorm : (CFSG.pCore 2 (Equiv.Perm (Fin 3))).Normal := CFSG.pCore_normal
    have hP : IsPGroup 2 (CFSG.pCore 2 (Equiv.Perm (Fin 3))) := CFSG.pCore_isPGroup
    have hconj : τ * σ * τ⁻¹ ∈ CFSG.pCore 2 (Equiv.Perm (Fin 3)) :=
      hnorm.conj_mem σ hσ τ
    have hmul : σ * (τ * σ * τ⁻¹) ∈ CFSG.pCore 2 (Equiv.Perm (Fin 3)) :=
      Subgroup.mul_mem _ hσ hconj
    obtain ⟨j, hj⟩ := hP ⟨_, hmul⟩
    have hpow : (σ * (τ * σ * τ⁻¹)) ^ (2 ^ j) = 1 := by
      simpa using congrArg Subtype.val hj
    have h3dvd : orderOf (σ * (τ * σ * τ⁻¹)) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have h2dvd : orderOf (σ * (τ * σ * τ⁻¹)) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hpow
    have hgcd : Nat.gcd 3 (2 ^ j) = 1 := Nat.Coprime.pow_right j (by norm_num)
    have hone : orderOf (σ * (τ * σ * τ⁻¹)) = 1 := by
      have := Nat.dvd_gcd h3dvd h2dvd
      rwa [hgcd, Nat.dvd_one] at this
    exact h1 (orderOf_eq_one_iff.mp hone)
  ·
    by_contra h
    haveI : (CFSG.pCore 2 (Equiv.Perm (Fin k))).Normal := CFSG.pCore_normal
    have hnt : Nontrivial (CFSG.pCore 2 (Equiv.Perm (Fin k))) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr h
    have hcard : 5 ≤ Nat.card (Fin k) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      exact hk
    have hA :=
      Equiv.Perm.alternatingGroup_le_of_normal (α := Fin k) hcard hnt
    let x0 : Fin k := ⟨0, by omega⟩
    let x1 : Fin k := ⟨1, by omega⟩
    let x2 : Fin k := ⟨2, by omega⟩
    have h01 : x0 ≠ x1 := by simp [x0, x1, Fin.ext_iff]
    have h02 : x0 ≠ x2 := by simp [x0, x2, Fin.ext_iff]
    have h12 : x1 ≠ x2 := by simp [x1, x2, Fin.ext_iff]
    have hc3 : (Equiv.swap x0 x1 * Equiv.swap x0 x2).IsThreeCycle :=
      Equiv.Perm.isThreeCycle_swap_mul_swap_same h01 h02 h12
    have hcN : Equiv.swap x0 x1 * Equiv.swap x0 x2 ∈
        CFSG.pCore 2 (Equiv.Perm (Fin k)) :=
      hA hc3.mem_alternatingGroup
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Equiv.Perm (Fin k)))
      (⟨Equiv.swap x0 x1 * Equiv.swap x0 x2, hcN⟩ :
        CFSG.pCore 2 (Equiv.Perm (Fin k)))
    have hpow : (Equiv.swap x0 x1 * Equiv.swap x0 x2) ^ (2 ^ j) = 1 := by
      simpa using congrArg Subtype.val hj
    have h3 : orderOf (Equiv.swap x0 x1 * Equiv.swap x0 x2) ∣ 2 ^ j :=
      orderOf_dvd_of_pow_eq_one hpow
    rw [hc3.orderOf] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at this

theorem range_ofSubtype_eq_fixingSubgroup {m : ℕ} {a b : Fin m} :
    (Equiv.Perm.ofSubtype (p := fun x : Fin m => x ≠ a ∧ x ≠ b)).range =
      fixingSubgroup (Equiv.Perm (Fin m)) ({a, b} : Set (Fin m)) := by
  ext g
  rw [Equiv.Perm.mem_range_ofSubtype_iff, mem_fixingSubgroup_iff]
  constructor
  · intro h y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hya | hyb
    · subst y
      by_contra hga
      exact (h (by simpa [Equiv.Perm.mem_support] using hga)).1 rfl
    · subst y
      by_contra hgb
      exact (h (by simpa [Equiv.Perm.mem_support] using hgb)).2 rfl
  · intro h x hx
    have hx' : g x ≠ x := by simpa [Equiv.Perm.mem_support] using hx
    constructor
    · intro hxa
      exact hx' (by simpa [hxa] using (h a (by simp)))
    · intro hxb
      exact hx' (by simpa [hxb] using (h b (by simp)))

theorem map_cenGen {G H : Type} [Group G] [Group H] (φ : G ≃* H) (D : Set G) (d : G) :
    (CFSG.RankThree.GF2n.Tim79a.cenGen D d).map φ.toMonoidHom =
      CFSG.RankThree.GF2n.Tim79a.cenGen (φ '' D) (φ d) := by
  rw [CFSG.RankThree.GF2n.Tim79a.cenGen, CFSG.RankThree.GF2n.Tim79a.cenGen,
    MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨hyD, hyC⟩, rfl⟩
    refine ⟨⟨y, hyD, rfl⟩, ?_⟩
    have hyC' : y * d = d * y := (Subgroup.mem_centralizer_singleton_iff).mp hyC
    exact (Subgroup.mem_centralizer_singleton_iff).mpr (by simpa using congrArg φ hyC')
  · rintro ⟨⟨y, hyD, rfl⟩, hxC⟩
    refine ⟨y, ⟨hyD, ?_⟩, rfl⟩
    have hxC' : φ y * φ d = φ d * φ y := (Subgroup.mem_centralizer_singleton_iff).mp hxC
    exact (Subgroup.mem_centralizer_singleton_iff).mpr (φ.injective (by simpa using hxC'))

theorem map_inSubgroup_pCore_map {G H : Type} [Group G] [Group H] (φ : G ≃* H)
    (K : Subgroup G) :
    (CFSG.inSubgroup (CFSG.pCore 2) K).map φ.toMonoidHom =
      CFSG.inSubgroup (CFSG.pCore 2) (K.map φ.toMonoidHom) := by
  let K' : Subgroup H := K.map φ.toMonoidHom
  let e : K ≃* K' := φ.subgroupMap K
  have hpc : (CFSG.pCore 2 K).map e.toMonoidHom = CFSG.pCore 2 K' :=
    CFSG.pCore_map_iso 2 e
  rw [CFSG.inSubgroup, CFSG.inSubgroup, ← hpc, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem noSqE1_of_map_mulEquiv {G H : Type} [Group G] [Group H]
    (φ : G ≃* H) {D : Set G} {D0 : Set H} (hD : D0 = φ '' D)
    (h : CFSG.RankThree.GF2n.Tim79a.NoSqE1 D0) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D := by
  intro d hd
  have hd0 : φ d ∈ D0 := by
    rw [hD]
    exact ⟨d, hd, rfl⟩
  have hle := h (φ d) hd0
  have hle' := Subgroup.map_mono (f := φ.symm.toMonoidHom) hle
  have hcen : (CFSG.RankThree.GF2n.Tim79a.cenGen D0 (φ d)).map φ.symm.toMonoidHom =
      CFSG.RankThree.GF2n.Tim79a.cenGen D d := by
    rw [hD, ← map_cenGen φ D d, Subgroup.map_map]
    simp
  have hcenter : (Subgroup.center H).map φ.symm.toMonoidHom = Subgroup.center G := by
    simpa using Subgroup.map_center_eq (φ.symm : H ≃* G)
  have hright : (Subgroup.zpowers (φ d) ⊔ Subgroup.center H).map φ.symm.toMonoidHom =
      Subgroup.zpowers d ⊔ Subgroup.center G := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hcenter]
    simp
  rw [map_inSubgroup_pCore_map, hcen, hright] at hle'
  exact hle'

theorem pCore_cenGen_swap_le {m : ℕ} (hm : m = 5 ∨ 7 ≤ m) {a b : Fin m} (hab : a ≠ b) :
    CFSG.inSubgroup (CFSG.pCore 2)
      (CFSG.RankThree.GF2n.Tim79a.cenGen {σ : Equiv.Perm (Fin m) | σ.IsSwap}
        (Equiv.swap a b)) ≤ Subgroup.zpowers (Equiv.swap a b) := by
  classical
  let p : Fin m → Prop := fun x => x ≠ a ∧ x ≠ b
  let N : Subgroup (Equiv.Perm (Fin m)) := Subgroup.zpowers (Equiv.swap a b)
  let P : Subgroup (Equiv.Perm (Fin m)) :=
    fixingSubgroup (Equiv.Perm (Fin m)) ({a, b} : Set (Fin m))
  let K : Subgroup (Equiv.Perm (Fin m)) := N ⊔ P
  let dK : K := ⟨Equiv.swap a b, Subgroup.mem_sup_left (Subgroup.mem_zpowers _)⟩
  have hcen : CFSG.RankThree.GF2n.Tim79a.cenGen {σ : Equiv.Perm (Fin m) | σ.IsSwap}
      (Equiv.swap a b) = K := by
    apply le_antisymm
    · rw [CFSG.RankThree.GF2n.Tim79a.cenGen]
      rw [Subgroup.closure_le]
      rintro e ⟨heD0, heC⟩
      obtain ⟨u, v, huv, rfl⟩ := heD0
      by_cases hsame : Equiv.swap u v = Equiv.swap a b
      · rw [hsame]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · have hcomm : Equiv.swap a b * Equiv.swap u v =
            Equiv.swap u v * Equiv.swap a b := by
          exact (Subgroup.mem_centralizer_singleton_iff.mp heC).symm
        have hdist := CFSG.Timmesfeld.Transvection.QTwo.disjoint_of_swap_commute
          (a := a) (b := b) (c := u) (d := v) hab huv
          (by intro h; exact hsame h.symm) hcomm
        refine Subgroup.mem_sup_right ?_
        change Equiv.swap u v ∈
          fixingSubgroup (Equiv.Perm (Fin m)) ({a, b} : Set (Fin m))
        rw [mem_fixingSubgroup_iff]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · simpa using Equiv.swap_apply_of_ne_of_ne hdist.1 hdist.2.1
        · simpa using Equiv.swap_apply_of_ne_of_ne hdist.2.2.1 hdist.2.2.2
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        refine Subgroup.subset_closure ⟨?_, ?_⟩
        · exact ⟨a, b, hab, rfl⟩
        · exact (Subgroup.mem_centralizer_singleton_iff).mpr rfl
      · have hrange := range_ofSubtype_eq_fixingSubgroup (a := a) (b := b) (m := m)
        change fixingSubgroup (Equiv.Perm (Fin m)) ({a, b} : Set (Fin m)) ≤
          CFSG.RankThree.GF2n.Tim79a.cenGen {σ : Equiv.Perm (Fin m) | σ.IsSwap}
            (Equiv.swap a b)
        rw [← hrange, MonoidHom.range_eq_map (Equiv.Perm.ofSubtype (p := p))]
        have htop : Subgroup.closure {σ : Equiv.Perm (Subtype p) | σ.IsSwap} = ⊤ :=
          Equiv.Perm.closure_isSwap
        rw [← htop, MonoidHom.map_closure]
        rw [Subgroup.closure_le]
        rintro _ ⟨σ, hσ, rfl⟩
        obtain ⟨u, v, huv, rfl⟩ := hσ
        rw [Equiv.Perm.ofSubtype_swap_eq]
        have huv' : (u : Fin m) ≠ (v : Fin m) := fun h => huv (Subtype.ext h)
        refine Subgroup.subset_closure ⟨⟨u, v, huv', rfl⟩, ?_⟩
        exact (Subgroup.mem_centralizer_singleton_iff).mpr
          (CFSG.Timmesfeld.Transvection.QTwo.swap_commute_of_ne
            hab huv' (Ne.symm u.2.1) (Ne.symm v.2.1)
            (Ne.symm u.2.2) (Ne.symm v.2.2)).symm
  rw [hcen]
  have hpresN : ∀ n ∈ N, ∀ y : Fin m, p y → p (n y) := by
    intro n hn y hy
    change n ∈ Subgroup.zpowers (Equiv.swap a b) at hn
    rw [Subgroup.mem_zpowers_iff] at hn
    obtain ⟨k, rfl⟩ := hn
    have hdy : Equiv.swap a b y = y := Equiv.swap_apply_of_ne_of_ne hy.1 hy.2
    rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (f := Equiv.swap a b) hdy k]
    exact hy
  have hpresP : ∀ q ∈ P, ∀ y : Fin m, p y → p (q y) := by
    intro q hq y hy
    change q ∈ fixingSubgroup (Equiv.Perm (Fin m)) ({a, b} : Set (Fin m)) at hq
    have hqa : q a = a := by
      simpa using (mem_fixingSubgroup_iff (M := Equiv.Perm (Fin m))
        (s := ({a, b} : Set (Fin m)))).mp hq a (by simp)
    have hqb : q b = b := by
      simpa using (mem_fixingSubgroup_iff (M := Equiv.Perm (Fin m))
        (s := ({a, b} : Set (Fin m)))).mp hq b (by simp)
    exact ⟨fun h => hy.1 (q.injective (by rw [h, hqa])),
      fun h => hy.2 (q.injective (by rw [h, hqb]))⟩
  let S : Subgroup (Equiv.Perm (Fin m)) :=
    { carrier := {x | ∀ y : Fin m, p y → p (x y)}
      one_mem' := by intro y hy; simpa using hy
      mul_mem' := by
        intro x y hx hy z hz
        rw [Equiv.Perm.mul_apply]
        exact hx (y z) (hy z hz)
      inv_mem' := by
        intro x hx y hy
        have hinj : Function.Injective
            (fun z : Subtype p => (⟨x z.1, hx z.1 z.2⟩ : Subtype p)) := by
          intro a b hab
          exact Subtype.ext (x.injective (Subtype.ext_iff.mp hab))
        have hsurj : Function.Surjective
            (fun z : Subtype p => (⟨x z.1, hx z.1 z.2⟩ : Subtype p)) :=
          Finite.injective_iff_surjective.mp hinj
        obtain ⟨z, hz⟩ := hsurj ⟨y, hy⟩
        have hzy : x z.1 = y := Subtype.ext_iff.mp hz
        rw [← hzy]
        simpa using z.2 }
  have hpresK : ∀ x ∈ K, ∀ y : Fin m, p y → p (x y) := by
    have hNle : N ≤ S := by
      intro n hn y hy
      exact hpresN n hn y hy
    have hPle : P ≤ S := by
      intro q hq y hy
      exact hpresP q hq y hy
    have hKle : K ≤ S := sup_le hNle hPle
    intro x hx y hy
    exact hKle hx y hy
  have hcardp : Fintype.card {x : Fin m // p x} = m - 2 := by
    have hcomp : Fintype.card {x : Fin m // ¬ p x} = 2 := by
      have h2 : Fintype.card {x : Fin m // x = a ∨ x = b} = 2 :=
        Fintype.card_subtype_eq_or_eq_of_ne hab
      rw [← h2]
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight fun x => by
        simp only [p, ne_eq, not_and, not_not]
        tauto
    have hcompl := Fintype.card_subtype_compl (p := p)
    rw [hcomp, Fintype.card_fin] at hcompl
    omega
  have hkminus : m - 2 = 3 ∨ 5 ≤ m - 2 := by omega
  let e : {x : Fin m // p x} ≃ Fin (m - 2) := Fintype.equivFinOfCardEq hcardp
  have hpbot : CFSG.pCore 2 (Equiv.Perm (Subtype p)) = ⊥ := by
    have hmap := CFSG.pCore_map_iso (p := 2) (f := Equiv.permCongrHom e)
    rw [pCore_two_perm_eq_bot_of_three_or_five_le hkminus] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (Equiv.permCongrHom e).injective).mp hmap
  let f : K →* Equiv.Perm (Subtype p) :=
    { toFun := fun x => (x : Equiv.Perm (Fin m)).subtypePerm fun y => by
        constructor
        · intro hy
          have h1 := hpresK (x⁻¹) (K.inv_mem x.2) ((x : Equiv.Perm (Fin m)) y) hy
          simpa using h1
        · intro hy
          exact hpresK x x.2 y hy
      map_one' := by
        ext y
        simp [Equiv.Perm.subtypePerm_apply]
      map_mul' := by
        intro x y
        exact Equiv.ext fun z => rfl }
  have hf_surj : Function.Surjective f := by
    intro σ
    refine ⟨⟨Equiv.Perm.ofSubtype σ, ?_⟩, ?_⟩
    · refine Subgroup.mem_sup_right ?_
      change Equiv.Perm.ofSubtype σ ∈
        fixingSubgroup (Equiv.Perm (Fin m)) ({a, b} : Set (Fin m))
      rw [mem_fixingSubgroup_iff]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hya | hyb
      · subst y
        have hnp : ¬ p a := by simp [p]
        simpa using Equiv.Perm.ofSubtype_apply_of_not_mem σ hnp
      · subst y
        have hnp : ¬ p b := by simp [p]
        simpa using Equiv.Perm.ofSubtype_apply_of_not_mem σ hnp
    · exact Equiv.ext fun z => Subtype.ext (by
        simp [f, Equiv.Perm.subtypePerm_apply])
  have hker : f.ker = Subgroup.zpowers dK := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hfix : ∀ y : Fin m, p y → (x : Equiv.Perm (Fin m)) y = y := by
        intro y hy
        have h1 := congrArg (fun σ : Equiv.Perm (Subtype p) => σ ⟨y, hy⟩) hx
        simpa [f, Equiv.Perm.subtypePerm_apply] using h1
      have hfix' : ∀ y : Fin m, y ≠ a → y ≠ b → (x : Equiv.Perm (Fin m)) y = y :=
        fun y hya hyb => hfix y ⟨hya, hyb⟩
      rcases eq_one_or_eq_swap_of_eq_on_compl hab hfix' with hx1 | hxd
      · rw [show x = 1 from Subtype.ext hx1]
        exact Subgroup.one_mem _
      · rw [show x = dK from Subtype.ext hxd]
        exact Subgroup.mem_zpowers dK
    · intro hx
      rw [Subgroup.mem_zpowers_iff] at hx
      obtain ⟨k, rfl⟩ := hx
      have hfd : f dK = 1 := by
        exact Equiv.ext fun z => Subtype.ext (by
          change Equiv.swap a b (z : Fin m) = (z : Fin m)
          exact Equiv.swap_apply_of_ne_of_ne z.2.1 z.2.2)
      rw [map_zpow, hfd, one_zpow]
  have hker_le : CFSG.pCore 2 K ≤ f.ker := by
    have hmap : (CFSG.pCore 2 K).map f ≤ CFSG.pCore 2 (Equiv.Perm (Subtype p)) := by
      refine le_sSup ?_
      exact ⟨Subgroup.Normal.map CFSG.pCore_normal f hf_surj,
        CFSG.pCore_isPGroup.map f⟩
    rw [hpbot] at hmap
    have hbot : (CFSG.pCore 2 K).map f = ⊥ := eq_bot_iff.mpr hmap
    exact (Subgroup.map_eq_bot_iff (CFSG.pCore 2 K)).mp hbot
  intro x hx
  rw [CFSG.inSubgroup] at hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyker : y ∈ f.ker := hker_le hy
  rw [hker] at hyker
  have hy' : (y : Equiv.Perm (Fin m)) ∈ (Subgroup.zpowers dK).map K.subtype :=
    ⟨y, hyker, rfl⟩
  have hy'' : (y : Equiv.Perm (Fin m)) ∈ Subgroup.zpowers (K.subtype dK) := by
    rw [← MonoidHom.map_zpowers]
    exact hy'
  simpa using hy''

theorem noSqE1_isSwap_perm {m : ℕ} (hm : m = 5 ∨ 7 ≤ m) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 {σ : Equiv.Perm (Fin m) | σ.IsSwap} := by
  intro d hd
  obtain ⟨a, b, hab, rfl⟩ := hd
  exact (pCore_cenGen_swap_le hm hab).trans le_sup_left

theorem noSqE1_of_pair_perm_of_ne_six
    {G : Type} [Group G] [Finite G] {D : Set G}
    (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    {m : ℕ} (hm : m = 5 ∨ 7 ≤ m)
    (φ : G ≃* Equiv.Perm (Fin m)) (hφ : ∀ g, g ∈ D ↔ (φ g).IsSwap) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D := by
  have hD : {σ : Equiv.Perm (Fin m) | σ.IsSwap} = φ '' D := by
    ext σ
    constructor
    · intro hσ
      refine ⟨φ.symm σ, ?_, φ.apply_symm_apply σ⟩
      exact (hφ (φ.symm σ)).2 (by simpa using hσ)
    · rintro ⟨g, hg, rfl⟩
      exact (hφ g).1 hg
  exact noSqE1_of_map_mulEquiv φ hD (noSqE1_isSwap_perm hm)

end CFSG.OddTranspositions
