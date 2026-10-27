module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagSz
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagL2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagU3
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
public import CFSG.GroupTheory.IsComponentOfMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.GorensteinWalter

variable {A B : Type} [Group A] [Group B]

theorem map_fst_prod (C : Subgroup A) (D : Subgroup B) :
    (C.prod D).map (MonoidHom.fst A B) = C := by
  ext a
  constructor
  · rintro ⟨⟨a', b⟩, h, rfl⟩
    exact h.1
  · intro ha
    exact ⟨(a, 1), ⟨ha, D.one_mem⟩, rfl⟩

theorem map_snd_prod (C : Subgroup A) (D : Subgroup B) :
    (C.prod D).map (MonoidHom.snd A B) = D := by
  ext b
  constructor
  · rintro ⟨⟨a, b'⟩, h, rfl⟩
    exact h.2
  · intro hb
    exact ⟨(1, b), ⟨C.one_mem, hb⟩, rfl⟩

theorem prod_lt_prod_right {C : Subgroup A} {D E : Subgroup B} (h : D < E) :
    C.prod D < C.prod E := by
  refine lt_of_le_of_ne (Subgroup.prod_mono le_rfl h.le) ?_
  intro heq
  apply h.ne
  have := congrArg (Subgroup.map (MonoidHom.snd A B)) heq
  simpa [map_snd_prod] using this

theorem prod_lt_prod_left {C E : Subgroup A} {D : Subgroup B} (h : C < E) :
    C.prod D < E.prod D := by
  refine lt_of_le_of_ne (Subgroup.prod_mono h.le le_rfl) ?_
  intro heq
  apply h.ne
  have := congrArg (Subgroup.map (MonoidHom.fst A B)) heq
  simpa [map_fst_prod] using this

theorem normalizer_prod_eq' {C : Subgroup A} {D : Subgroup B} :
    Subgroup.normalizer ((C.prod D : Subgroup (A × B)) : Set (A × B)) =
      (Subgroup.normalizer (C : Set A)).prod (Subgroup.normalizer (D : Set B)) := by
  ext x
  rw [Subgroup.mem_prod]
  constructor
  · intro hx
    rw [Subgroup.mem_normalizer_iff] at hx
    constructor
    · rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        have hmem : x * (a, 1) * x⁻¹ ∈ C.prod D :=
          (hx (a, 1)).mp (Subgroup.mem_prod.mpr ⟨ha, by simpa using D.one_mem⟩)
        exact (Subgroup.mem_prod.mp hmem).1
      · intro ha
        have hmem : x * (a, 1) * x⁻¹ ∈ C.prod D :=
          Subgroup.mem_prod.mpr ⟨ha, by simpa using D.one_mem⟩
        exact (Subgroup.mem_prod.mp ((hx (a, 1)).mpr hmem)).1
    · rw [Subgroup.mem_normalizer_iff]
      intro b
      constructor
      · intro hb
        have hmem : x * (1, b) * x⁻¹ ∈ C.prod D :=
          (hx (1, b)).mp (Subgroup.mem_prod.mpr ⟨by simpa using C.one_mem, hb⟩)
        exact (Subgroup.mem_prod.mp hmem).2
      · intro hb
        have hmem : x * (1, b) * x⁻¹ ∈ C.prod D :=
          Subgroup.mem_prod.mpr ⟨by simpa using C.one_mem, hb⟩
        exact (Subgroup.mem_prod.mp ((hx (1, b)).mpr hmem)).2
  · rintro ⟨hx1, hx2⟩
    rw [Subgroup.mem_normalizer_iff] at hx1 hx2 ⊢
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_prod] at hy ⊢
      exact ⟨(hx1 y.1).mp hy.1, (hx2 y.2).mp hy.2⟩
    · intro hy
      rw [Subgroup.mem_prod] at hy ⊢
      exact ⟨(hx1 y.1).mpr hy.1, (hx2 y.2).mpr hy.2⟩

theorem not_normal_of_isCoatom_of_normalizer_sylow {G : Type} [Group G] [Finite G]
    {C : Subgroup G} (hC : IsCoatom C) {S : Sylow 2 G}
    (hCS : C = Subgroup.normalizer (S : Set G)) : ¬ C.Normal := by
  intro hnorm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSnormal : S.Normal := Sylow.normal_of_normalizer_normal S (hCS ▸ hnorm)
  exact hC.ne_top (hCS.trans (Subgroup.normalizer_eq_top_iff.mpr hSnormal))

theorem comap_inl_normal_of_map_fst_eq_top [Finite A] [Finite B]
    {H : Subgroup (A × B)} (h : H.map (MonoidHom.fst A B) = ⊤) :
    (H.comap (MonoidHom.inl A B)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_comap] at hn ⊢
  have hg : g ∈ H.map (MonoidHom.fst A B) := by rw [h]; exact Subgroup.mem_top g
  obtain ⟨⟨g', b⟩, hgb, hgg⟩ := Subgroup.mem_map.mp hg
  have hgg' : g' = g := by simpa using hgg
  rw [hgg'] at hgb
  have hconj := H.mul_mem (H.mul_mem hgb hn) (H.inv_mem hgb)
  simpa using hconj

theorem comap_inr_normal_of_map_snd_eq_top [Finite A] [Finite B]
    {H : Subgroup (A × B)} (h : H.map (MonoidHom.snd A B) = ⊤) :
    (H.comap (MonoidHom.inr A B)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_comap] at hn ⊢
  have hg : g ∈ H.map (MonoidHom.snd A B) := by rw [h]; exact Subgroup.mem_top g
  obtain ⟨⟨a, g'⟩, hgb, hgg⟩ := Subgroup.mem_map.mp hg
  have hgg' : g' = g := by simpa using hgg
  rw [hgg'] at hgb
  have hconj := H.mul_mem (H.mul_mem hgb hn) (H.inv_mem hgb)
  simpa using hconj

theorem prod_overgroup_classification [Finite A] [Finite B]
    {C : Subgroup A} {D : Subgroup B} (hC : IsCoatom C) (hD : IsCoatom D)
    (hCn : ¬ C.Normal) (hDn : ¬ D.Normal) {H : Subgroup (A × B)} (hH : C.prod D ≤ H) :
    H = C.prod D ∨ H = C.prod ⊤ ∨ H = (⊤ : Subgroup A).prod D ∨ H = ⊤ := by
  have hCA : C ≤ H.map (MonoidHom.fst A B) := by
    rw [← map_fst_prod C D]
    exact Subgroup.map_mono hH
  have hDB : D ≤ H.map (MonoidHom.snd A B) := by
    rw [← map_snd_prod C D]
    exact Subgroup.map_mono hH
  have hAK : C ≤ H.comap (MonoidHom.inl A B) := by
    intro c hc
    rw [Subgroup.mem_comap]
    exact hH (Subgroup.mem_prod.mpr ⟨hc, D.one_mem⟩)
  have hDK : D ≤ H.comap (MonoidHom.inr A B) := by
    intro d hd
    rw [Subgroup.mem_comap]
    exact hH (Subgroup.mem_prod.mpr ⟨C.one_mem, hd⟩)
  rcases hC.le_iff.mp hCA with hAtop | hAC
  ·
    have hKA : (H.comap (MonoidHom.inl A B)).Normal :=
      comap_inl_normal_of_map_fst_eq_top hAtop
    have hKAtop : H.comap (MonoidHom.inl A B) = ⊤ := by
      rcases hC.le_iff.mp hAK with h | h
      · exact h
      · rw [h] at hKA
        exact absurd hKA hCn
    have hA1 : (⊤ : Subgroup A).prod (⊥ : Subgroup B) ≤ H := by
      rintro ⟨a, b⟩ hx
      rw [Subgroup.mem_prod] at hx
      have hb : b = 1 := Subgroup.mem_bot.mp hx.2
      have hmem : a ∈ H.comap (MonoidHom.inl A B) := by
        rw [hKAtop]; exact Subgroup.mem_top a
      rw [Subgroup.mem_comap] at hmem
      simpa [hb] using hmem
    rcases hD.le_iff.mp hDB with hBtop | hBD
    ·
      have hKB : (H.comap (MonoidHom.inr A B)).Normal :=
        comap_inr_normal_of_map_snd_eq_top hBtop
      have hKBtop : H.comap (MonoidHom.inr A B) = ⊤ := by
        rcases hD.le_iff.mp hDK with h | h
        · exact h
        · rw [h] at hKB
          exact absurd hKB hDn
      have hB1 : (⊥ : Subgroup A).prod (⊤ : Subgroup B) ≤ H := by
        rintro ⟨a, b⟩ hx
        rw [Subgroup.mem_prod] at hx
        have ha : a = 1 := Subgroup.mem_bot.mp hx.1
        have hmem : b ∈ H.comap (MonoidHom.inr A B) := by
          rw [hKBtop]; exact Subgroup.mem_top b
        rw [Subgroup.mem_comap] at hmem
        simpa [ha] using hmem
      refine Or.inr (Or.inr (Or.inr (top_unique ?_)))
      rintro ⟨a, b⟩ -
      have ha1 : (a, 1) ∈ H :=
        hA1 (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top a, Subgroup.mem_bot.mpr rfl⟩)
      have h1b : (1, b) ∈ H :=
        hB1 (Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top b⟩)
      simpa using H.mul_mem ha1 h1b
    ·
      have hHle : H ≤ (⊤ : Subgroup A).prod D := by
        intro x hx
        rw [Subgroup.mem_prod]
        refine ⟨Subgroup.mem_top _, ?_⟩
        have hmem : x.2 ∈ H.map (MonoidHom.snd A B) := Subgroup.mem_map_of_mem _ hx
        rwa [hBD] at hmem
      refine Or.inr (Or.inr (Or.inl (le_antisymm hHle ?_)))
      intro x hx
      rw [Subgroup.mem_prod] at hx
      have ha1 : (x.1, 1) ∈ H :=
        hA1 (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩)
      have h1d : (1, x.2) ∈ H := hH (Subgroup.mem_prod.mpr ⟨C.one_mem, hx.2⟩)
      simpa using H.mul_mem ha1 h1d
  ·
    rcases hD.le_iff.mp hDB with hBtop | hBD
    ·
      have hKB : (H.comap (MonoidHom.inr A B)).Normal :=
        comap_inr_normal_of_map_snd_eq_top hBtop
      have hKBtop : H.comap (MonoidHom.inr A B) = ⊤ := by
        rcases hD.le_iff.mp hDK with h | h
        · exact h
        · rw [h] at hKB
          exact absurd hKB hDn
      have hB1 : (⊥ : Subgroup A).prod (⊤ : Subgroup B) ≤ H := by
        rintro ⟨a, b⟩ hx
        rw [Subgroup.mem_prod] at hx
        have ha : a = 1 := Subgroup.mem_bot.mp hx.1
        have hmem : b ∈ H.comap (MonoidHom.inr A B) := by
          rw [hKBtop]; exact Subgroup.mem_top b
        rw [Subgroup.mem_comap] at hmem
        simpa [ha] using hmem
      have hHle : H ≤ C.prod ⊤ := by
        intro x hx
        rw [Subgroup.mem_prod]
        refine ⟨?_, Subgroup.mem_top _⟩
        have hmem : x.1 ∈ H.map (MonoidHom.fst A B) := Subgroup.mem_map_of_mem _ hx
        rwa [hAC] at hmem
      refine Or.inr (Or.inl (le_antisymm hHle ?_))
      intro x hx
      rw [Subgroup.mem_prod] at hx
      have hc1 : (x.1, 1) ∈ H := hH (Subgroup.mem_prod.mpr ⟨hx.1, D.one_mem⟩)
      have h1b : (1, x.2) ∈ H :=
        hB1 (Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top _⟩)
      simpa using H.mul_mem hc1 h1b
    ·
      have hHle : H ≤ C.prod D := by
        intro x hx
        rw [Subgroup.mem_prod]
        constructor
        · have hmem : x.1 ∈ H.map (MonoidHom.fst A B) := Subgroup.mem_map_of_mem _ hx
          rwa [hAC] at hmem
        · have hmem : x.2 ∈ H.map (MonoidHom.snd A B) := Subgroup.mem_map_of_mem _ hx
          rwa [hBD] at hmem
      exact Or.inl (le_antisymm hHle hH)

theorem map_eq_of_odd_order_of_sq {G : Type} [Group G] {θ : MulAut G}
    (hodd : Odd (orderOf θ)) {P : Subgroup G}
    (h2 : P.map (θ * θ).toMonoidHom = P) : P.map θ.toMonoidHom = P := by
  obtain ⟨k, hk⟩ := hodd
  have hθeq : θ = (θ * θ) ^ (k + 1) := by
    have hpow : θ ^ (2 * (k + 1)) = θ := by
      rw [show 2 * (k + 1) = orderOf θ + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
    calc θ = θ ^ (2 * (k + 1)) := hpow.symm
      _ = (θ * θ) ^ (k + 1) := by rw [← pow_two, ← pow_mul]
  have hmap : ∀ n : ℕ, P.map (((θ * θ) ^ n)).toMonoidHom = P := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, MulAut.one_def]
        exact Subgroup.map_id P
    | succ n ih =>
        rw [pow_succ]
        rw [show (((θ * θ) ^ n * (θ * θ))).toMonoidHom =
          ((θ * θ) ^ n).toMonoidHom.comp (θ * θ).toMonoidHom from rfl]
        rw [← Subgroup.map_map, h2, ih]
  rw [hθeq]
  exact hmap (k + 1)

theorem card_prod_lt_prod_top [Finite A] [Finite B] {C : Subgroup A} {D : Subgroup B}
    (hD : IsCoatom D) :
    Nat.card (C.prod D : Subgroup (A × B)) <
      Nat.card (C.prod (⊤ : Subgroup B) : Subgroup (A × B)) :=
  Subgroup.card_lt_of_lt (prod_lt_prod_right (C := C) hD.lt_top)

theorem card_prod_top_lt_top [Finite A] [Finite B] {C : Subgroup A} (hC : IsCoatom C) :
    Nat.card (C.prod (⊤ : Subgroup B) : Subgroup (A × B)) <
      Nat.card (⊤ : Subgroup (A × B)) := by
  refine Subgroup.card_lt_of_lt ?_
  have h := prod_lt_prod_left (D := (⊤ : Subgroup B)) (E := (⊤ : Subgroup A)) hC.lt_top
  simpa using h

theorem card_prod_lt_top_prod [Finite A] [Finite B] {C : Subgroup A} {D : Subgroup B}
    (hC : IsCoatom C) :
    Nat.card (C.prod D : Subgroup (A × B)) <
      Nat.card ((⊤ : Subgroup A).prod D : Subgroup (A × B)) :=
  Subgroup.card_lt_of_lt (prod_lt_prod_left (D := D) hC.lt_top)

theorem card_top_prod_lt_top [Finite A] [Finite B] {D : Subgroup B} (hD : IsCoatom D) :
    Nat.card ((⊤ : Subgroup A).prod D : Subgroup (A × B)) <
      Nat.card (⊤ : Subgroup (A × B)) := by
  refine Subgroup.card_lt_of_lt ?_
  have h := prod_lt_prod_right (C := (⊤ : Subgroup A)) (E := (⊤ : Subgroup B)) hD.lt_top
  simpa using h

theorem map_mul_apply {G : Type} [Group G] (θ φ : MulAut G) (P : Subgroup G) :
    P.map (θ * φ).toMonoidHom = (P.map φ.toMonoidHom).map θ.toMonoidHom := by
  rw [show (θ * φ).toMonoidHom = θ.toMonoidHom.comp φ.toMonoidHom from rfl,
    ← Subgroup.map_map]

theorem overgroup_card_middle_of_ne [Finite A] [Finite B]
    {C : Subgroup A} {D : Subgroup B} (hC : IsCoatom C) (hD : IsCoatom D)
    (hCn : ¬ C.Normal) (hDn : ¬ D.Normal) {R : Subgroup (A × B)} (hR : C.prod D ≤ R)
    (h0 : Nat.card R ≠ Nat.card (C.prod D : Subgroup (A × B)))
    (htop : Nat.card R ≠ Nat.card (⊤ : Subgroup (A × B))) :
    R = C.prod ⊤ ∨ R = (⊤ : Subgroup A).prod D := by
  rcases prod_overgroup_classification hC hD hCn hDn hR with h | h | h | h
  · rw [h] at h0
    exact absurd rfl h0
  · exact Or.inl h
  · exact Or.inr h
  · rw [h] at htop
    exact absurd rfl htop

theorem IsCoatom.map_of_surjective_of_ker_le {G H : Type} [Group G] [Group H]
    {N : Subgroup G} (hN : IsCoatom N) (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ N) : IsCoatom (N.map f) := by
  constructor
  · intro htop
    apply hN.ne_top
    rw [eq_top_iff]
    intro g _
    have hmem : f g ∈ N.map f := htop ▸ Subgroup.mem_top (f g)
    obtain ⟨n, hn, hgn⟩ := Subgroup.mem_map.mp hmem
    have hker_mem : g * n⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hgn, mul_inv_cancel]
    have hgn' : g * n⁻¹ ∈ N := hker hker_mem
    have := N.mul_mem hgn' hn
    simpa using this
  · intro K hK
    rw [eq_top_iff]
    intro y _
    have hNK : N ≤ K.comap f := by
      intro n hn
      exact Subgroup.mem_comap.mpr (hK.le (Subgroup.mem_map_of_mem f hn))
    have hNK_ne : N ≠ K.comap f := by
      intro heq
      have hKm : K = N.map f := by
        rw [← Subgroup.map_comap_eq_self_of_surjective hf K, heq]
      exact hK.ne hKm.symm
    have hKtop : K.comap f = ⊤ := by
      rcases hN.le_iff.mp hNK with h | h
      · exact h
      · exact absurd h.symm hNK_ne
    obtain ⟨g, rfl⟩ := hf y
    have hg : g ∈ K.comap f := by
      rw [hKtop]
      exact Subgroup.mem_top g
    exact Subgroup.mem_comap.mp hg

theorem IsCoatom.of_map_of_surjective_of_ker_le {G H : Type} [Group G] [Group H]
    {N : Subgroup G} (f : G →* H) (hf : Function.Surjective f) (hker : f.ker ≤ N)
    (h : IsCoatom (N.map f)) : IsCoatom N := by
  constructor
  · intro htop
    apply h.ne_top
    rw [htop, Subgroup.map_top_of_surjective f hf]
  · intro K hK
    have hle : N.map f ≤ K.map f := Subgroup.map_mono hK.le
    rcases h.le_iff.mp hle with htop | heq
    · rw [eq_top_iff]
      intro g _
      have hmem : f g ∈ K.map f := htop ▸ Subgroup.mem_top (f g)
      obtain ⟨k, hk, hfg⟩ := Subgroup.mem_map.mp hmem
      have hker' : g * k⁻¹ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hfg, mul_inv_cancel]
      have hgN : g * k⁻¹ ∈ N := hker hker'
      have := K.mul_mem (hK.le hgN) hk
      simpa using this
    · have hKc : (K.map f).comap f = K := Subgroup.comap_map_eq_self (hker.trans hK.le)
      have hNc : (N.map f).comap f = N := Subgroup.comap_map_eq_self hker
      have hKN : K = N := by rw [← hKc, ← hNc, heq]
      exact absurd hKN.symm hK.ne

theorem coatom_normalizer_sylow_psl2 (K : Type) [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) :
    ∀ S : Sylow 2 (PSL2 K), IsCoatom (Subgroup.normalizer (S : Set (PSL2 K))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S₀
  let U : Sylow 2 (PSL2 K) := psl2UpperUnipotentSylow K hK
  let Usub : Subgroup (PSL2 K) := (U : Subgroup (PSL2 K))
  have hU : Usub = psl2UpperUnipotentSubgroup K :=
    psl2UpperUnipotentSylow_coe K hK
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2 K) U S₀
  have hS₀eq : (S₀ : Subgroup (PSL2 K)) =
      Usub.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hset : (S₀ : Set (PSL2 K)) =
      ((Usub.map (MulAut.conj g).toMonoidHom : Subgroup (PSL2 K)) : Set (PSL2 K)) :=
    congrArg (fun H : Subgroup (PSL2 K) => (H : Set (PSL2 K))) hS₀eq
  have hN : Subgroup.normalizer (S₀ : Set (PSL2 K)) =
      (Subgroup.normalizer (Usub : Set (PSL2 K))).map
        (MulAut.conj g).toMonoidHom := by
    rw [hset]
    exact (Subgroup.map_equiv_normalizer_eq Usub (MulAut.conj g)).symm
  have hB : Subgroup.normalizer (Usub : Set (PSL2 K)) = psl2Borel K := by
    rw [hU]
    exact psl2UpperUnipotent_normalizer_eq_borel K
  have hNborel : Subgroup.normalizer (S₀ : Set (PSL2 K)) =
      (psl2Borel K).map (MulAut.conj g).toMonoidHom := by
    rw [hN, hB]
  rw [hNborel]
  exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj g))
    (psl2Borel K)).2 (CFSG.Quasithin.H13.P31X.l2_psl2Borel_isCoatom K)

theorem coatom_normalizer_sylow_of_isL2 {n : ℕ} {X : Type} [Group X] [Finite X]
    (hX : IsL2 X n) :
    ∀ S : Sylow 2 X, IsCoatom (Subgroup.normalizer (S : Set X)) := by
  have hX' : CFSG.Blueprint.LieModel X .PSL 2 2 n := hX
  have ht : (CFSG.Open.StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
  have hmodel : CFSG.Open.StatedClassicalModel X .PSL 2 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX' ht
  rw [CFSG.Open.StatedClassicalModel] at hmodel
  obtain ⟨hadm, K, hfield, hfinite, hcard, ⟨e₀⟩⟩ := hmodel
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : Fintype K := Fintype.ofFinite K
  rw [CFSG.Open.StatedLieAdmissible] at hadm
  have hn1 : 1 ≤ n := hadm.2.1
  have hEven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hcard]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
  have hchar : ringChar K = 2 := FiniteField.even_card_iff_char_two.mpr hEven
  haveI : CharP K 2 := ringChar.of_eq hchar
  exact isCoatom_normalizer_sylow_of_mulEquiv
    (e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)
    (coatom_normalizer_sylow_psl2 K hcard)

theorem coatom_normalizer_sylow_of_isSz {n : ℕ} {X : Type} [Group X] [Finite X]
    (hX : IsSz X n) :
    ∀ S : Sylow 2 X, IsCoatom (Subgroup.normalizer (S : Set X)) := by
  have hSuz : CFSG.Blueprint.SuzukiModel X 2 n :=
    (CFSG.Blueprint.LieModel.suzukiModel hX).2
  obtain ⟨-, a, ha, K, hfield, hfinite, rfl, hcard, ⟨e⟩⟩ := hSuz
  letI : Field K := hfield
  letI : Finite K := hfinite
  exact isCoatom_normalizer_sylow_of_mulEquiv e
    (isCoatom_normalizer_sylow_suzukiGroup ha hcard)

theorem map_fix_of_prod_overgroups [Finite A] [Finite B]
    {C : Subgroup A} {D : Subgroup B} (hC : IsCoatom C) (hD : IsCoatom D)
    (hCn : ¬ C.Normal) (hDn : ¬ D.Normal)
    (θ : MulAut (A × B)) (hθodd : Odd (orderOf θ))
    (hθN : (C.prod D).map θ.toMonoidHom = C.prod D)
    {P : Subgroup (A × B)} (hP : C.prod D ≤ P) :
    P.map θ.toMonoidHom = P := by
  have h01 := card_prod_lt_prod_top (C := C) hD
  have h13 : Nat.card (C.prod (⊤ : Subgroup B) : Subgroup (A × B)) <
      Nat.card (⊤ : Subgroup (A × B)) := card_prod_top_lt_top (C := C) hC
  have h02 := card_prod_lt_top_prod (D := D) hC
  have h23 : Nat.card ((⊤ : Subgroup A).prod D : Subgroup (A × B)) <
      Nat.card (⊤ : Subgroup (A × B)) := card_top_prod_lt_top (D := D) hD
  have hB1neB2 : (C.prod ⊤ : Subgroup (A × B)) ≠ (⊤ : Subgroup A).prod D := by
    intro heq
    have h := congrArg (Subgroup.map (MonoidHom.fst A B)) heq
    simp only [map_fst_prod] at h
    exact hC.ne_top h
  have hθPge : C.prod D ≤ P.map θ.toMonoidHom := by
    rw [← hθN]
    exact Subgroup.map_mono hP
  have hcardθP : Nat.card (P.map θ.toMonoidHom : Subgroup (A × B)) = Nat.card P :=
    Subgroup.card_map_of_injective θ.injective
  rcases prod_overgroup_classification hC hD hCn hDn hP with hP0 | hP1 | hP2 | hP3
  ·
    rw [hP0] at hθPge hcardθP ⊢
    rcases prod_overgroup_classification hC hD hCn hDn hθPge with h | h | h | h
    · exact h
    · rw [h] at hcardθP
      omega
    · rw [h] at hcardθP
      omega
    · rw [h] at hcardθP
      exact absurd hcardθP (ne_of_lt (lt_trans h01 h13)).symm
  ·
    rw [hP1] at hθPge hcardθP ⊢
    rcases prod_overgroup_classification hC hD hCn hDn hθPge with h | h | h | h
    · rw [h] at hcardθP
      omega
    · exact h
    · exfalso
      have hQge : C.prod D ≤ ((C.prod ⊤ : Subgroup (A × B)).map θ.toMonoidHom).map θ.toMonoidHom := by
        rw [← hθN]
        exact Subgroup.map_mono hθPge
      have hQcard : Nat.card (((C.prod ⊤ : Subgroup (A × B)).map θ.toMonoidHom).map θ.toMonoidHom) =
          Nat.card ((C.prod ⊤ : Subgroup (A × B)).map θ.toMonoidHom) :=
        Subgroup.card_map_of_injective θ.injective
      have hQclass : ((C.prod ⊤ : Subgroup (A × B)).map θ.toMonoidHom).map θ.toMonoidHom =
            C.prod ⊤ ∨ ((C.prod ⊤ : Subgroup (A × B)).map θ.toMonoidHom).map θ.toMonoidHom =
            (⊤ : Subgroup A).prod D := by
        refine overgroup_card_middle_of_ne hC hD hCn hDn hQge ?_ ?_
        · rw [hQcard, h]
          exact (ne_of_lt h02).symm
        · rw [hQcard, h]
          exact ne_of_lt h23
      rcases hQclass with hsq | hsq
      · have hsq' : (C.prod ⊤ : Subgroup (A × B)).map (θ * θ).toMonoidHom = C.prod ⊤ := by
          rw [map_mul_apply, hsq]
        have hfix := map_eq_of_odd_order_of_sq hθodd hsq'
        have heq : (⊤ : Subgroup A).prod D = C.prod ⊤ := by
          rw [← h, hfix]
        exact absurd heq.symm hB1neB2
      · have hsame : ((C.prod ⊤ : Subgroup (A × B)).map θ.toMonoidHom).map θ.toMonoidHom =
            (C.prod ⊤ : Subgroup (A × B)).map θ.toMonoidHom := by
          rw [hsq, h]
        have hinj := (Subgroup.map_injective θ.injective) hsame
        have heq : (⊤ : Subgroup A).prod D = C.prod ⊤ := by
          rw [← h, hinj]
        exact absurd heq.symm hB1neB2
    · rw [h] at hcardθP
      exact absurd hcardθP (ne_of_lt h13).symm
  ·
    rw [hP2] at hθPge hcardθP ⊢
    rcases prod_overgroup_classification hC hD hCn hDn hθPge with h | h | h | h
    · rw [h] at hcardθP
      omega
    · exfalso
      have hQge : C.prod D ≤ (((⊤ : Subgroup A).prod D : Subgroup (A × B)).map θ.toMonoidHom).map θ.toMonoidHom := by
        rw [← hθN]
        exact Subgroup.map_mono hθPge
      have hQcard : Nat.card ((((⊤ : Subgroup A).prod D : Subgroup (A × B)).map θ.toMonoidHom).map θ.toMonoidHom) =
          Nat.card (((⊤ : Subgroup A).prod D : Subgroup (A × B)).map θ.toMonoidHom) :=
        Subgroup.card_map_of_injective θ.injective
      have hQclass : (((⊤ : Subgroup A).prod D : Subgroup (A × B)).map θ.toMonoidHom).map θ.toMonoidHom =
            C.prod ⊤ ∨ (((⊤ : Subgroup A).prod D : Subgroup (A × B)).map θ.toMonoidHom).map θ.toMonoidHom =
            (⊤ : Subgroup A).prod D := by
        refine overgroup_card_middle_of_ne hC hD hCn hDn hQge ?_ ?_
        · rw [hQcard, h]
          exact (ne_of_lt h01).symm
        · rw [hQcard, h]
          exact ne_of_lt h13
      rcases hQclass with hsq | hsq
      · have hsame : (((⊤ : Subgroup A).prod D : Subgroup (A × B)).map θ.toMonoidHom).map θ.toMonoidHom =
            ((⊤ : Subgroup A).prod D : Subgroup (A × B)).map θ.toMonoidHom := by
          rw [hsq, h]
        have hinj := (Subgroup.map_injective θ.injective) hsame
        have heq : C.prod ⊤ = (⊤ : Subgroup A).prod D := by
          rw [← h, hinj]
        exact absurd heq hB1neB2
      · have hsq' : ((⊤ : Subgroup A).prod D : Subgroup (A × B)).map (θ * θ).toMonoidHom =
            (⊤ : Subgroup A).prod D := by
          rw [map_mul_apply, hsq]
        have hfix := map_eq_of_odd_order_of_sq hθodd hsq'
        have heq : C.prod ⊤ = (⊤ : Subgroup A).prod D := by
          rw [← h, hfix]
        exact absurd heq hB1neB2
    · exact h
    · rw [h] at hcardθP
      exact absurd hcardθP (ne_of_lt h23).symm
  ·
    rw [hP3] at hθPge hcardθP ⊢
    rcases prod_overgroup_classification hC hD hCn hDn hθPge with h | h | h | h
    · rw [h] at hcardθP
      exact absurd hcardθP (ne_of_lt (lt_trans h01 h13))
    · rw [h] at hcardθP
      exact absurd hcardθP (ne_of_lt h13)
    · rw [h] at hcardθP
      exact absurd hcardθP (ne_of_lt h23)
    · exact h

theorem kDiag_prod_of_coatom_normalizer [Finite A] [Finite B]
    (hcoatA : ∀ S : Sylow 2 A, IsCoatom (Subgroup.normalizer (S : Set A)))
    (hcoatB : ∀ S : Sylow 2 B, IsCoatom (Subgroup.normalizer (S : Set B))) :
    ∀ (θ : MulAut (A × B)), Odd (orderOf θ) →
    ∀ S : Sylow 2 (A × B),
      (∀ x ∈ (S : Subgroup (A × B)), θ x ∈ (S : Subgroup (A × B))) →
    ∀ P : Subgroup (A × B), IsParabolicTwo (A × B) P →
      (S : Subgroup (A × B)) ≤ Subgroup.normalizer (P : Set (A × B)) →
      ∀ x ∈ P, θ x ∈ P := by
  intro θ hθ S hSθ P hP hSP x hx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSmap : (S : Subgroup (A × B)).map θ.toMonoidHom = S := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hSθ y hy
    · rw [Subgroup.card_map_of_injective θ.injective]
  have hfst : Function.Surjective (MonoidHom.fst A B) := fun a => ⟨(a, 1), rfl⟩
  have hsnd : Function.Surjective (MonoidHom.snd A B) := fun b => ⟨(1, b), rfl⟩
  let SA : Sylow 2 A := S.mapSurjective (f := MonoidHom.fst A B) hfst
  let SB : Sylow 2 B := S.mapSurjective (f := MonoidHom.snd A B) hsnd
  have hSAcoe : (SA : Subgroup A) = (S : Subgroup (A × B)).map (MonoidHom.fst A B) :=
    Sylow.coe_mapSurjective (f := MonoidHom.fst A B) hfst S
  have hSBcoe : (SB : Subgroup B) = (S : Subgroup (A × B)).map (MonoidHom.snd A B) :=
    Sylow.coe_mapSurjective (f := MonoidHom.snd A B) hsnd S
  have hSsplit : (S : Subgroup (A × B)) = SA.prod SB := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro y hy
      rw [Subgroup.mem_prod]
      exact ⟨hSAcoe ▸ Subgroup.mem_map_of_mem _ hy, hSBcoe ▸ Subgroup.mem_map_of_mem _ hy⟩
    · have hcardS : Nat.card (S : Subgroup (A × B)) =
          2 ^ (Nat.card (A × B)).factorization 2 := Sylow.card_eq_multiplicity S
      have hcardA : Nat.card (SA : Subgroup A) = 2 ^ (Nat.card A).factorization 2 :=
        Sylow.card_eq_multiplicity SA
      have hcardB : Nat.card (SB : Subgroup B) = 2 ^ (Nat.card B).factorization 2 :=
        Sylow.card_eq_multiplicity SB
      have hcardprod : Nat.card (SA.prod SB : Subgroup (A × B)) =
          Nat.card (SA : Subgroup A) * Nat.card (SB : Subgroup B) := by
        rw [Nat.card_congr (Subgroup.prodEquiv (SA : Subgroup A) (SB : Subgroup B)).toEquiv,
          Nat.card_prod]
      have hfac : (Nat.card (A × B)).factorization 2 =
          (Nat.card A).factorization 2 + (Nat.card B).factorization 2 := by
        rw [Nat.card_prod A B,
          Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne')]
        rfl
      exact le_of_eq (by
        calc Nat.card (SA.prod SB : Subgroup (A × B))
            = Nat.card (SA : Subgroup A) * Nat.card (SB : Subgroup B) := hcardprod
          _ = 2 ^ (Nat.card A).factorization 2 * 2 ^ (Nat.card B).factorization 2 := by
                rw [hcardA, hcardB]
          _ = 2 ^ ((Nat.card A).factorization 2 + (Nat.card B).factorization 2) := by
                rw [← pow_add]
          _ = 2 ^ (Nat.card (A × B)).factorization 2 := by rw [hfac]
          _ = Nat.card (S : Subgroup (A × B)) := by rw [hcardS])
  have hN : Subgroup.normalizer ((S : Subgroup (A × B)) : Set (A × B)) =
      (Subgroup.normalizer (SA : Set A)).prod (Subgroup.normalizer (SB : Set B)) := by
    rw [hSsplit]
    exact normalizer_prod_eq'
  have hSP' : (S : Subgroup (A × B)) ≤ P :=
    IsParabolicTwo.le_of_le_normalizer hP S.isPGroup' hSP
  have hNP : Subgroup.normalizer ((S : Subgroup (A × B)) : Set (A × B)) ≤ P :=
    hP.normalizer_le S hSP'
  have hNP' : (Subgroup.normalizer (SA : Set A)).prod (Subgroup.normalizer (SB : Set B)) ≤ P := by
    rw [← hN]
    exact hNP
  have hθN : (Subgroup.normalizer ((S : Subgroup (A × B)) : Set (A × B))).map θ.toMonoidHom =
      Subgroup.normalizer ((S : Subgroup (A × B)) : Set (A × B)) := by
    rw [Subgroup.map_equiv_normalizer_eq (S : Subgroup (A × B)) θ, hSmap]
  have hθN' : ((Subgroup.normalizer (SA : Set A)).prod
        (Subgroup.normalizer (SB : Set B))).map θ.toMonoidHom =
      (Subgroup.normalizer (SA : Set A)).prod (Subgroup.normalizer (SB : Set B)) := by
    rw [← hN]
    exact hθN
  have hfixP : P.map θ.toMonoidHom = P :=
    map_fix_of_prod_overgroups (hcoatA SA) (hcoatB SB)
      (not_normal_of_isCoatom_of_normalizer_sylow (hcoatA SA) rfl)
      (not_normal_of_isCoatom_of_normalizer_sylow (hcoatB SB) rfl)
      θ hθ hθN' hNP'
  exact hfixP ▸ Subgroup.mem_map_of_mem θ.toMonoidHom hx

theorem kDiag_of_isSzL2Product {n : ℕ} {X : Type} [Group X] [Finite X]
    (hX : IsSzL2Product X n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ P : Subgroup X, IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  obtain ⟨A, B, hAgrp, hBgrp, ⟨e⟩, hAb, hBb⟩ := hX
  letI : Group A := hAgrp
  letI : Group B := hBgrp
  haveI : Finite (A × B) := Finite.of_injective (e.symm : A × B → X) e.symm.injective
  haveI : Finite A := Finite.of_injective (fun a : A => (a, (1 : B)))
    (by intro a₁ a₂ h; exact (Prod.ext_iff.mp h).1)
  haveI : Finite B := Finite.of_injective (fun b : B => ((1 : A), b))
    (by intro b₁ b₂ h; exact (Prod.ext_iff.mp h).2)
  have hcoatA : ∀ S : Sylow 2 A, IsCoatom (Subgroup.normalizer (S : Set A)) := by
    rcases hAb with h | h
    · exact coatom_normalizer_sylow_of_isSz h
    · exact coatom_normalizer_sylow_of_isL2 h
  have hcoatB : ∀ S : Sylow 2 B, IsCoatom (Subgroup.normalizer (S : Set B)) := by
    rcases hBb with h | h
    · exact coatom_normalizer_sylow_of_isSz h
    · exact coatom_normalizer_sylow_of_isL2 h
  exact kDiag_transport e (kDiag_prod_of_coatom_normalizer hcoatA hcoatB)

theorem kDiag_of_centralQuotient_of_map {X : Type} [Group X] [Finite X]
    {I : Subgroup X} [I.Normal] (hI : I ≤ Subgroup.center X)
    (hquot : ∀ (θbar : MulAut (X ⧸ I)), Odd (orderOf θbar) →
      ∀ Sbar : Sylow 2 (X ⧸ I),
        (∀ y ∈ (Sbar : Subgroup (X ⧸ I)),
          θbar y ∈ (Sbar : Subgroup (X ⧸ I))) →
      ∀ Pbar : Subgroup (X ⧸ I),
        IsParabolicTwo (X ⧸ I) Pbar →
        (Sbar : Subgroup (X ⧸ I)) ≤
          Subgroup.normalizer (Pbar : Set (X ⧸ I)) →
        ∀ y ∈ Pbar, θbar y ∈ Pbar) :
    ∀ (θ : MulAut X), Odd (orderOf θ) → I.map θ = I →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ (P : Subgroup X), IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  intro θ hθ hθI S hSθ P hP hSP x hx
  let π : X →* X ⧸ I := QuotientGroup.mk' I
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective I
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let θbar : MulAut (X ⧸ I) := QuotientGroup.congr I I θ hθI
  have hθbar_mk : ∀ y : X, θbar (π y) = π (θ y) := fun y =>
    QuotientGroup.congr_mk' I I θ hθI y
  have hpow : θbar ^ orderOf θ = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective I y
    have h : ∀ m : ℕ, ∀ z : X, (θbar ^ m) (π z) = π ((θ ^ m) z) := by
      intro m
      induction m with
      | zero => intro z; rfl
      | succ m ih =>
          intro z
          rw [pow_succ]
          change (θbar ^ m) (θbar (π z)) = _
          rw [hθbar_mk, ih]
          rw [pow_succ]
          rfl
    rw [h (orderOf θ) x, pow_orderOf_eq_one, MulAut.one_apply, MulAut.one_apply]
  have hθbar_odd : Odd (orderOf θbar) :=
    hθ.of_dvd_nat (orderOf_dvd_iff_pow_eq_one.mpr hpow)
  let Sbar : Sylow 2 (X ⧸ I) := S.mapSurjective (f := π) hπ
  have hSbar_coe : (Sbar : Subgroup (X ⧸ I)) = (S : Subgroup X).map π :=
    Sylow.coe_mapSurjective (f := π) hπ S
  have hSbarθ : ∀ y ∈ (Sbar : Subgroup (X ⧸ I)), θbar y ∈ (Sbar : Subgroup (X ⧸ I)) := by
    intro y hy
    rw [hSbar_coe] at hy ⊢
    obtain ⟨s, hs, hys⟩ := Subgroup.mem_map.mp hy
    rw [← hys, hθbar_mk]
    exact Subgroup.mem_map_of_mem π (hSθ s hs)
  have hPbar : IsParabolicTwo (X ⧸ I) (P.map π) := hP.map π hπ
  have hSPbar : (Sbar : Subgroup (X ⧸ I)) ≤
      Subgroup.normalizer ((P.map π : Subgroup (X ⧸ I)) : Set (X ⧸ I)) := by
    rw [hSbar_coe]
    exact (Subgroup.map_mono hSP).trans (Subgroup.le_normalizer_map (f := π) (H := P))
  have hfix := hquot θbar hθbar_odd Sbar hSbarθ (P.map π) hPbar hSPbar
  have hIP : I ≤ P := hI.trans hP.center_le
  have hPcomap : (P.map π).comap π = P :=
    Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hIP)
  have hmem : π (θ x) ∈ P.map π := by
    have h1 := hfix (π x) (Subgroup.mem_map_of_mem π hx)
    rwa [hθbar_mk] at h1
  rw [show P = (P.map π).comap π from hPcomap.symm, Subgroup.mem_comap]
  exact hmem

theorem coatom_normalizer_sylow_of_isSU3 {n : ℕ} {X : Type} [Group X] [Finite X]
    (hX : IsSU3 X n) :
    ∀ S : Sylow 2 X, IsCoatom (Subgroup.normalizer (S : Set X)) := by
  obtain ⟨hQ, hU3⟩ := hX
  let Z : Subgroup X := Subgroup.center X
  haveI : Z.Normal := inferInstance
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S
  let Sbar : Sylow 2 (X ⧸ Z) := S.mapSurjective (f := π) hπsurj
  have hSbarcoe : (Sbar : Subgroup (X ⧸ Z)) = (S : Subgroup X).map π :=
    Sylow.coe_mapSurjective (f := π) hπsurj S
  have hmapN : (Subgroup.normalizer (S : Set X)).map π =
      Subgroup.normalizer ((Sbar : Subgroup (X ⧸ Z)) : Set (X ⧸ Z)) := by
    rw [hSbarcoe]
    exact (normalizer_map_sylow_eq π hπsurj S).symm
  have hkerN : π.ker ≤ Subgroup.normalizer (S : Set X) := by
    rw [QuotientGroup.ker_mk']
    exact Subgroup.center_le_normalizer _
  refine IsCoatom.of_map_of_surjective_of_ker_le π hπsurj hkerN ?_
  rw [hmapN]
  exact coatom_normalizer_sylow_of_isU3 hU3 Sbar

theorem kDiag_of_isSU3CentralSquare {X : Type} [Group X] [Finite X]
    (hX : IsSU3CentralSquare X) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ P : Subgroup X, IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  obtain ⟨K₁, K₂, hsup, hcomm, hSU3₁, hSU3₂, hIcard⟩ := hX
  have hK₂n : K₂.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine le_antisymm le_top ?_
    rw [← hsup]
    refine sup_le ?_ Subgroup.le_normalizer
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    ext b
    constructor
    · rintro ⟨c, hc, rfl⟩
      change a * c * a⁻¹ ∈ K₂
      rw [hcomm a ha c hc]
      simpa using hc
    · intro hb
      refine ⟨b, hb, ?_⟩
      change a * b * a⁻¹ = b
      rw [hcomm a ha b hb]
      group
  have hK₁n : K₁.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine le_antisymm le_top ?_
    rw [← hsup]
    refine sup_le Subgroup.le_normalizer ?_
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    ext a
    constructor
    · rintro ⟨c, hc, rfl⟩
      change b * c * b⁻¹ ∈ K₁
      rw [← hcomm c hc b hb]
      simpa using hc
    · intro ha
      refine ⟨a, ha, ?_⟩
      change b * a * b⁻¹ = a
      rw [← hcomm a ha b hb]
      group
  haveI : K₁.Normal := hK₁n
  haveI : K₂.Normal := hK₂n
  have hIcenter : K₁ ⊓ K₂ ≤ Subgroup.center X := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := K₁) (t := K₂) (x := x)).mp
        (by rw [hsup]; exact Subgroup.mem_top x)
    calc (a * b) * z = a * (b * z) := by group
      _ = a * (z * b) := by rw [← hcomm z hz.1 b hb]
      _ = (a * z) * b := by group
      _ = (z * a) * b := by rw [hcomm a ha z hz.2]
      _ = z * (a * b) := by group
  have hc₁ : CFSG.Open.IsComponentOf K₁ ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal hK₁n), hSU3₁.1⟩
  have hc₂ : CFSG.Open.IsComponentOf K₂ ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal hK₂n), hSU3₂.1⟩
  intro θ hθ S hSθ P hP hSP x hx
  have hθK₁or : K₁.map θ.toMonoidHom = K₁ ∨ K₁.map θ.toMonoidHom = K₂ := by
    have hcomp : CFSG.Open.IsComponentOf (K₁.map θ.toMonoidHom) ⊤ := by
      have h := CFSG.isComponentOf_map_mulEquiv θ hc₁
      rwa [Subgroup.map_top_of_surjective θ.toMonoidHom θ.surjective] at h
    rcases uc22p22r_component_le_or_le hsup hcomp with hle | hle
    · exact Or.inl (CFSG.ComponentClassification.LocalComponents.eq_of_le _ _ hcomp hc₁ hle)
    · exact Or.inr (CFSG.ComponentClassification.LocalComponents.eq_of_le _ _ hcomp hc₂ hle)
  have hθK₂or : K₂.map θ.toMonoidHom = K₂ ∨ K₂.map θ.toMonoidHom = K₁ := by
    have hcomp : CFSG.Open.IsComponentOf (K₂.map θ.toMonoidHom) ⊤ := by
      have h := CFSG.isComponentOf_map_mulEquiv θ hc₂
      rwa [Subgroup.map_top_of_surjective θ.toMonoidHom θ.surjective] at h
    rcases uc22p22r_component_le_or_le hsup hcomp with hle | hle
    · exact Or.inr (CFSG.ComponentClassification.LocalComponents.eq_of_le _ _ hcomp hc₁ hle)
    · exact Or.inl (CFSG.ComponentClassification.LocalComponents.eq_of_le _ _ hcomp hc₂ hle)
  have hθ2K₁ : K₁.map (θ * θ).toMonoidHom = K₁ := by
    rw [map_mul_apply]
    rcases hθK₁or with h | h
    · rw [h]
      exact h
    · rw [h]
      rcases hθK₂or with h2 | h2
      · rw [h2]
        exact ((Subgroup.map_injective θ.injective) (h.trans h2.symm)).symm
      · rw [h2]
  have hθ2K₂ : K₂.map (θ * θ).toMonoidHom = K₂ := by
    rw [map_mul_apply]
    rcases hθK₂or with h | h
    · rw [h]
      exact h
    · rw [h]
      rcases hθK₁or with h2 | h2
      · rw [h2]
        exact ((Subgroup.map_injective θ.injective) (h.trans h2.symm)).symm
      · rw [h2]
  have hθK₁ : K₁.map θ.toMonoidHom = K₁ := map_eq_of_odd_order_of_sq hθ hθ2K₁
  have hθK₂ : K₂.map θ.toMonoidHom = K₂ := map_eq_of_odd_order_of_sq hθ hθ2K₂
  have hθI : (K₁ ⊓ K₂).map θ.toMonoidHom = K₁ ⊓ K₂ := by
    rw [Subgroup.map_inf _ _ _ θ.injective, hθK₁, hθK₂]
  let I : Subgroup X := K₁ ⊓ K₂
  haveI : I.Normal := Subgroup.normal_inf_normal K₁ K₂
  let π : X →* X ⧸ I := QuotientGroup.mk' I
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective I
  let A : Subgroup (X ⧸ I) := K₁.map π
  let B : Subgroup (X ⧸ I) := K₂.map π
  have hIcenter' : I ≤ Subgroup.center X := hIcenter
  have hθI' : I.map θ.toMonoidHom = I := hθI
  have hAsup : A ⊔ B = ⊤ := by
    change (K₁.map π) ⊔ (K₂.map π) = ⊤
    rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective π hπ]
  have hAcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k₁, hk₁, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨k₂, hk₂, rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hcomm k₁ hk₁ k₂ hk₂]
  have hAdisj : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_inf] at hz
    obtain ⟨k₁, hk₁, hk₁z⟩ := Subgroup.mem_map.mp hz.1
    obtain ⟨k₂, hk₂, hk₂z⟩ := Subgroup.mem_map.mp hz.2
    have heq : π k₁ = π k₂ := by rw [hk₁z, hk₂z]
    have hdiv : k₁ * k₂⁻¹ ∈ I := by
      have := QuotientGroup.eq_iff_div_mem.mp heq
      simpa [div_eq_mul_inv] using this
    have hk₁K₂ : k₁ ∈ K₂ := by
      have h1 : k₁ * k₂⁻¹ ∈ K₂ := hdiv.2
      have h2 : (k₁ * k₂⁻¹) * k₂ ∈ K₂ := K₂.mul_mem h1 hk₂
      simpa using h2
    have hk₁I : k₁ ∈ I := ⟨hk₁, hk₁K₂⟩
    have hπk₁ : π k₁ = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hk₁I
    rw [← hk₁z, hπk₁]
    exact Subgroup.mem_bot.mpr rfl
  have hBnormal : B.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine le_antisymm le_top ?_
    rw [← hAsup]
    refine sup_le ?_ Subgroup.le_normalizer
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    ext b
    constructor
    · rintro ⟨c, hc, rfl⟩
      change a * c * a⁻¹ ∈ B
      rw [hAcomm a ha c hc]
      simpa using hc
    · intro hb
      refine ⟨b, hb, ?_⟩
      change a * b * a⁻¹ = b
      rw [hAcomm a ha b hb]
      group
  haveI : B.Normal := hBnormal
  have hdecomp : ∀ {q : X ⧸ I}, q ∈ (⊤ : Subgroup (X ⧸ I)) →
      ∃ a ∈ A, ∃ b ∈ B, a * b = q := by
    intro q _
    have hq : q ∈ A ⊔ B := by rw [hAsup]; exact Subgroup.mem_top q
    exact (Subgroup.mem_sup_of_normal_right).mp hq
  let e₀ : (A × B) ≃* ↥(⊤ : Subgroup (X ⧸ I)) :=
    Subgroup.mulEquivProdOfInternalDirect A B ⊤ le_top le_top
      (fun {a b} ha hb => hAcomm a ha b hb) hAdisj hdecomp
  let e : (A × B) ≃* (X ⧸ I) := e₀.trans Subgroup.topEquiv
  have hcoatA : ∀ T : Sylow 2 A, IsCoatom (Subgroup.normalizer (T : Set A)) := by
    intro T
    let f₁ : ↥K₁ →* A := (π.comp K₁.subtype).codRestrict A (fun k =>
      Subgroup.mem_map_of_mem π k.2)
    have hf₁ : Function.Surjective f₁ := by
      intro a
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp a.2
      refine ⟨⟨k, hk⟩, ?_⟩
      exact Subtype.ext hkx
    obtain ⟨S₁, hS₁⟩ := Sylow.mapSurjective_surjective (f := f₁) hf₁ 2 T
    have hTcoe : (T : Subgroup A) = (S₁ : Subgroup ↥K₁).map f₁ := by
      rw [← hS₁, Sylow.coe_mapSurjective]
    have hTcoe' : (T : Set A) = (((S₁ : Subgroup ↥K₁).map f₁ : Subgroup A) : Set A) :=
      congrArg (fun H : Subgroup A => (H : Set A)) hTcoe
    rw [hTcoe', normalizer_map_sylow_eq f₁ hf₁ S₁]
    have hcoat₁ : IsCoatom (Subgroup.normalizer (S₁ : Set ↥K₁)) :=
      coatom_normalizer_sylow_of_isSU3 hSU3₁ S₁
    have hkerS₁ : f₁.ker ≤ Subgroup.normalizer (S₁ : Set ↥K₁) := by
      intro k hk
      have hkZ : (k : X) ∈ I := by
        have hkval : f₁ k = 1 := MonoidHom.mem_ker.mp hk
        have hval : ((f₁ k : A) : X ⧸ I) = π (k : X) := rfl
        have hπk : π (k : X) = 1 := by rw [← hval, hkval]; rfl
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hπk
        exact hπk
      have hkcenter : k ∈ Subgroup.center ↥K₁ := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact Subgroup.mem_center_iff.mp (hIcenter hkZ) (y : X)
      exact Subgroup.center_le_normalizer _ hkcenter
    exact IsCoatom.map_of_surjective_of_ker_le hcoat₁ f₁ hf₁ hkerS₁
  have hcoatB : ∀ T : Sylow 2 B, IsCoatom (Subgroup.normalizer (T : Set B)) := by
    intro T
    let f₂ : ↥K₂ →* B := (π.comp K₂.subtype).codRestrict B (fun k =>
      Subgroup.mem_map_of_mem π k.2)
    have hf₂ : Function.Surjective f₂ := by
      intro a
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp a.2
      refine ⟨⟨k, hk⟩, ?_⟩
      exact Subtype.ext hkx
    obtain ⟨S₂, hS₂⟩ := Sylow.mapSurjective_surjective (f := f₂) hf₂ 2 T
    have hTcoe : (T : Subgroup B) = (S₂ : Subgroup ↥K₂).map f₂ := by
      rw [← hS₂, Sylow.coe_mapSurjective]
    have hTcoe' : (T : Set B) = (((S₂ : Subgroup ↥K₂).map f₂ : Subgroup B) : Set B) :=
      congrArg (fun H : Subgroup B => (H : Set B)) hTcoe
    rw [hTcoe', normalizer_map_sylow_eq f₂ hf₂ S₂]
    have hcoat₂ : IsCoatom (Subgroup.normalizer (S₂ : Set ↥K₂)) :=
      coatom_normalizer_sylow_of_isSU3 hSU3₂ S₂
    have hkerS₂ : f₂.ker ≤ Subgroup.normalizer (S₂ : Set ↥K₂) := by
      intro k hk
      have hkZ : (k : X) ∈ I := by
        have hkval : f₂ k = 1 := MonoidHom.mem_ker.mp hk
        have hval : ((f₂ k : B) : X ⧸ I) = π (k : X) := rfl
        have hπk : π (k : X) = 1 := by rw [← hval, hkval]; rfl
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hπk
        exact hπk
      have hkcenter : k ∈ Subgroup.center ↥K₂ := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact Subgroup.mem_center_iff.mp (hIcenter hkZ) (y : X)
      exact Subgroup.center_le_normalizer _ hkcenter
    exact IsCoatom.map_of_surjective_of_ker_le hcoat₂ f₂ hf₂ hkerS₂
  have hQ : ∀ (θbar : MulAut (X ⧸ I)), Odd (orderOf θbar) →
      ∀ Sbar : Sylow 2 (X ⧸ I),
        (∀ y ∈ (Sbar : Subgroup (X ⧸ I)),
          θbar y ∈ (Sbar : Subgroup (X ⧸ I))) →
      ∀ Pbar : Subgroup (X ⧸ I),
        IsParabolicTwo (X ⧸ I) Pbar →
        (Sbar : Subgroup (X ⧸ I)) ≤
          Subgroup.normalizer (Pbar : Set (X ⧸ I)) →
        ∀ y ∈ Pbar, θbar y ∈ Pbar :=
    kDiag_transport e.symm (kDiag_prod_of_coatom_normalizer hcoatA hcoatB)
  exact kDiag_of_centralQuotient_of_map hIcenter' hQ θ hθ hθI' S hSθ P hP hSP x hx

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
