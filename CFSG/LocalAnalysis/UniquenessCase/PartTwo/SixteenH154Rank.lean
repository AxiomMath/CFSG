module

public import CFSG.LocalAnalysis.AGLEmbedding.AltBetaRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.Quasithin.EmptyFaithful.S151bModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16h_pow_apply_ne_self {W : Type} [CommGroup W] {U : Subgroup W} {p : ℕ}
    (hp : p.Prime) {e : MulAut W} (he : orderOf e = p)
    (hfix : ∀ u ∈ U, e u = u → u = 1) {u₀ : W} (hu₀ : u₀ ∈ U) (hne : u₀ ≠ 1)
    {k : ℕ} (hk0 : 0 < k) (hkp : k < p) : (e ^ k) u₀ ≠ u₀ := by
  intro h
  have hcop : Nat.Coprime k p :=
    ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hk0 hkp)).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hpow : ((e ^ k) ^ m) u₀ = u₀ := by
    clear hm
    induction m with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, MulAut.mul_apply, h]
        exact ih
  have hep : e ^ p = 1 := by rw [← he]; exact pow_orderOf_eq_one e
  have hmod : k * m ≡ 1 [MOD p] := by
    rw [Nat.ModEq, hm, Nat.mod_eq_of_lt hp.one_lt]
  have hekm : e ^ (k * m) = e := by
    have h1 := pow_eq_pow_of_modEq (x := e) hmod hep
    simpa using h1
  have heu : e u₀ = u₀ := by
    rw [← hekm, pow_mul]
    exact hpow
  exact hne (hfix u₀ hu₀ heu)

theorem s16h_exists_pow_of_commute {W : Type} [CommGroup W] [Finite W] {U : Subgroup W} {p : ℕ}
    (hp : p.Prime) {e c : MulAut W} (he : orderOf e = p) (hU : Nat.card ↥U = p + 1)
    (heU : ∀ u ∈ U, e u ∈ U) (hfix : ∀ u ∈ U, e u = u → u = 1) (hcU : ∀ u ∈ U, c u ∈ U)
    (hce : c * e = e * c) : ∃ j : ℕ, ∀ u ∈ U, c u = (e ^ j) u := by
  haveI : Fintype ↥U := Fintype.ofFinite _
  have hcardU : Fintype.card ↥U = p + 1 := by rw [← Nat.card_eq_fintype_card]; exact hU
  obtain ⟨u₀, hu₀ne'⟩ := Fintype.exists_ne_of_one_lt_card (a := (1 : ↥U))
    (by have := hp.two_le; omega)
  have hu₀ : (u₀ : W) ∈ U := u₀.2
  have hu₀ne : (u₀ : W) ≠ 1 := fun h => hu₀ne' (Subtype.ext h)
  have hU_i : ∀ i : ℕ, (e ^ i) (u₀ : W) ∈ U := by
    intro i
    induction i with
    | zero => simpa using hu₀
    | succ i ih => rw [pow_succ', MulAut.mul_apply]; exact heU _ ih
  have hne_i : ∀ i : ℕ, (e ^ i) (u₀ : W) ≠ 1 := by
    intro i h1
    have : (u₀ : W) = 1 := by
      have h2 : (e ^ i)⁻¹ ((e ^ i) (u₀ : W)) = (e ^ i)⁻¹ 1 := congrArg _ h1
      rw [MulAut.inv_apply_self, map_one] at h2
      exact h2
    exact hu₀ne this
  have hf_inj : Function.Injective (fun i : Fin p => (e ^ (i : ℕ)) (u₀ : W)) := by
    intro i j hij
    change (e ^ (i : ℕ)) (u₀ : W) = (e ^ (j : ℕ)) (u₀ : W) at hij
    by_contra hne
    have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hij' with hlt | hlt
    · have hle : (i : ℕ) ≤ (j : ℕ) := le_of_lt hlt
      have h1 : (e ^ (i : ℕ)) ((e ^ ((j : ℕ) - (i : ℕ))) (u₀ : W)) =
          (e ^ (i : ℕ)) (u₀ : W) := by
        rw [← MulAut.mul_apply, ← pow_add, Nat.add_sub_cancel' hle, hij]
      have h2 : (e ^ ((j : ℕ) - (i : ℕ))) (u₀ : W) = (u₀ : W) :=
        (e ^ (i : ℕ)).injective h1
      exact (s16h_pow_apply_ne_self hp he hfix hu₀ hu₀ne (by omega) (by omega)) h2
    · have hle : (j : ℕ) ≤ (i : ℕ) := le_of_lt hlt
      have h1 : (e ^ (j : ℕ)) ((e ^ ((i : ℕ) - (j : ℕ))) (u₀ : W)) =
          (e ^ (j : ℕ)) (u₀ : W) := by
        rw [← MulAut.mul_apply, ← pow_add, Nat.add_sub_cancel' hle, hij]
      have h2 : (e ^ ((i : ℕ) - (j : ℕ))) (u₀ : W) = (u₀ : W) :=
        (e ^ (j : ℕ)).injective h1
      exact (s16h_pow_apply_ne_self hp he hfix hu₀ hu₀ne (by omega) (by omega)) h2
  have hUncard : (U : Set W).ncard = p + 1 := by
    rw [← Nat.card_coe_set_eq]; exact hU
  let T : Set W := {u | u ∈ U ∧ u ≠ 1}
  have hT : T = (U : Set W) \ {1} := by ext u; simp [T]
  have hTcard : T.ncard = p := by
    rw [hT, Set.ncard_sdiff_singleton_of_mem (show (1 : W) ∈ (U : Set W) from U.one_mem),
      hUncard]
    omega
  have hsub : Set.range (fun i : Fin p => (e ^ (i : ℕ)) (u₀ : W)) ⊆ T := by
    rintro _ ⟨i, rfl⟩
    exact ⟨hU_i (i : ℕ), hne_i (i : ℕ)⟩
  have hrange : Set.range (fun i : Fin p => (e ^ (i : ℕ)) (u₀ : W)) = T := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    rw [Set.ncard_range_of_injective hf_inj, Nat.card_fin, hTcard]
  have hcU_mem : c (u₀ : W) ∈ T := by
    refine ⟨hcU _ hu₀, ?_⟩
    intro h1
    have : (u₀ : W) = 1 := by
      have h2 : c⁻¹ (c (u₀ : W)) = c⁻¹ 1 := congrArg _ h1
      rw [MulAut.inv_apply_self, map_one] at h2
      exact h2
    exact hu₀ne this
  have hcmem : c (u₀ : W) ∈ Set.range (fun i : Fin p => (e ^ (i : ℕ)) (u₀ : W)) := by
    rw [hrange]; exact hcU_mem
  obtain ⟨j, hj⟩ := hcmem
  change (e ^ (j : ℕ)) (u₀ : W) = c (u₀ : W) at hj
  refine ⟨(j : ℕ), ?_⟩
  intro u hu
  rcases eq_or_ne u 1 with rfl | hu1
  · simp
  · have humem : u ∈ Set.range (fun i : Fin p => (e ^ (i : ℕ)) (u₀ : W)) := by
      rw [hrange]; exact ⟨hu, hu1⟩
    obtain ⟨i, hi⟩ := humem
    change (e ^ (i : ℕ)) (u₀ : W) = u at hi
    have hcei : Commute c (e ^ (i : ℕ)) := (show Commute c e from hce).pow_right _
    calc c u = c ((e ^ (i : ℕ)) (u₀ : W)) := by rw [hi]
      _ = (c * e ^ (i : ℕ)) (u₀ : W) := rfl
      _ = (e ^ (i : ℕ) * c) (u₀ : W) := by rw [hcei.eq]
      _ = (e ^ (i : ℕ)) (c (u₀ : W)) := rfl
      _ = (e ^ (i : ℕ)) ((e ^ (j : ℕ)) (u₀ : W)) := by rw [hj]
      _ = (e ^ (i : ℕ) * e ^ (j : ℕ)) (u₀ : W) := rfl
      _ = (e ^ ((i : ℕ) + (j : ℕ))) (u₀ : W) := by rw [pow_add]
      _ = (e ^ ((j : ℕ) + (i : ℕ))) (u₀ : W) := by rw [Nat.add_comm]
      _ = (e ^ (j : ℕ) * e ^ (i : ℕ)) (u₀ : W) := by rw [pow_add]
      _ = (e ^ (j : ℕ)) ((e ^ (i : ℕ)) (u₀ : W)) := rfl
      _ = (e ^ (j : ℕ)) u := by rw [hi]

theorem s16h_fixes_of_commute_coprime {W : Type} [CommGroup W] [Finite W] {U : Subgroup W}
    {p : ℕ} (hp : p.Prime) {e c : MulAut W} (he : orderOf e = p) (hU : Nat.card ↥U = p + 1)
    (heU : ∀ u ∈ U, e u ∈ U) (hfix : ∀ u ∈ U, e u = u → u = 1) (hcU : ∀ u ∈ U, c u ∈ U)
    (hce : c * e = e * c) {m : ℕ} (hm : Nat.Coprime m p) (hcm : c ^ m = 1) :
    ∀ u ∈ U, c u = u := by
  obtain ⟨j, hj⟩ := s16h_exists_pow_of_commute hp he hU heU hfix hcU hce
  have hcUpow : ∀ n : ℕ, ∀ u ∈ U, (c ^ n) u ∈ U := by
    intro n
    induction n with
    | zero => intro u hu; simpa using hu
    | succ n ih =>
        intro u hu
        rw [pow_succ', MulAut.mul_apply]
        exact hcU _ (ih u hu)
  have hpow_c : ∀ n : ℕ, ∀ u ∈ U, ((e ^ j) ^ n) u = (c ^ n) u := by
    intro n
    induction n with
    | zero => intro u _; simp
    | succ n ih =>
        intro u hu
        calc ((e ^ j) ^ (n + 1)) u = (e ^ j) (((e ^ j) ^ n) u) := by
              rw [pow_succ', MulAut.mul_apply]
          _ = (e ^ j) ((c ^ n) u) := by rw [ih u hu]
          _ = c ((c ^ n) u) := (hj _ (hcUpow n u hu)).symm
          _ = (c ^ (n + 1)) u := by rw [pow_succ', MulAut.mul_apply]
  have hfix_pow : ∀ u ∈ U, (e ^ (j * m)) u = u := by
    intro u hu
    rw [pow_mul, hpow_c m u hu, hcm, MulAut.one_apply]
  have hdvd : p ∣ j * m := by
    by_contra hdvd
    have hcop : Nat.Coprime (j * m) p := (hp.coprime_iff_not_dvd.mpr hdvd).symm
    obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have hep : e ^ p = 1 := by rw [← he]; exact pow_orderOf_eq_one e
    have hmod : (j * m) * m' ≡ 1 [MOD p] := by
      rw [Nat.ModEq, hm', Nat.mod_eq_of_lt hp.one_lt]
    have hejmm' : e ^ ((j * m) * m') = e := by
      have h1 := pow_eq_pow_of_modEq (x := e) hmod hep
      simpa using h1
    have hiter : ∀ n : ℕ, ∀ u ∈ U, ((e ^ (j * m)) ^ n) u = u := by
      intro n
      induction n with
      | zero => intro u _; simp
      | succ n ih =>
          intro u hu
          rw [pow_succ, MulAut.mul_apply, hfix_pow u hu]
          exact ih u hu
    have hefix : ∀ u ∈ U, e u = u := by
      intro u hu
      rw [← hejmm', pow_mul]
      exact hiter m' u hu
    haveI : Fintype ↥U := Fintype.ofFinite _
    have hcardU : Fintype.card ↥U = p + 1 := by rw [← Nat.card_eq_fintype_card]; exact hU
    obtain ⟨u₀, hu₀⟩ := Fintype.exists_ne_of_one_lt_card (a := (1 : ↥U))
      (by have := hp.two_le; omega)
    exact hu₀ (Subtype.ext (hfix (u₀ : W) u₀.2 (hefix (u₀ : W) u₀.2)))
  intro u hu
  have hj1 : e ^ j = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [he]; exact (hm.symm).dvd_of_dvd_mul_right hdvd)
  rw [hj u hu, hj1, MulAut.one_apply]

private theorem s16h_mem_normalizer_conj {W : Type} [Group W]
    {L : Subgroup (MulAut W)} {k a : MulAut W}
    (hk : k ∈ normalizer ((L.map (MulAut.conj a).toMonoidHom : Subgroup (MulAut W)) :
      Set (MulAut W))) :
    a⁻¹ * k * a ∈ normalizer (L : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff] at hk ⊢
  intro l
  constructor
  · intro hl
    have hHl : a * l * a⁻¹ ∈ L.map (MulAut.conj a).toMonoidHom := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hl
      simpa [MulAut.conj_apply] using h
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp ((hk _).mp hHl)
    have hxeq' : a * x * a⁻¹ = k * (a * l * a⁻¹) * k⁻¹ := by
      simpa [MulAut.conj_apply] using hxeq
    have hxval : x = a⁻¹ * (k * (a * l * a⁻¹) * k⁻¹) * a := by
      rw [← hxeq']; group
    have hx' : (a⁻¹ * k * a) * l * (a⁻¹ * k * a)⁻¹ = x := by
      rw [hxval]; group
    rwa [hx']
  · intro h
    have hmem : a * ((a⁻¹ * k * a) * l * (a⁻¹ * k * a)⁻¹) * a⁻¹ ∈
        L.map (MulAut.conj a).toMonoidHom := by
      have h' := Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom h
      simpa [MulAut.conj_apply] using h'
    have heq : a * ((a⁻¹ * k * a) * l * (a⁻¹ * k * a)⁻¹) * a⁻¹ =
        k * (a * l * a⁻¹) * k⁻¹ := by group
    rw [heq] at hmem
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp ((hk _).mpr hmem)
    have hxeq' : a * x * a⁻¹ = a * l * a⁻¹ := by
      simpa [MulAut.conj_apply] using hxeq
    have hxl : x = l := by
      have h2 : a * x = a * l := mul_right_cancel hxeq'
      exact mul_left_cancel h2
    rwa [← hxl]

theorem s16h_eq_one_of_normalizes_conj {W : Type} [CommGroup W] [Finite W]
    {A L : Subgroup (MulAut W)} (hgen : (⨆ X ∈ conjSubs A (commSub ⊤ L), X) = ⊤)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥L p) (hU : Nat.card ↥(commSub ⊤ L) = p + 1)
    (hfix : commSub ⊤ L ⊓ fixV L = ⊥)
    (hχ : ∀ n ∈ A, n ∈ normalizer (L : Set (MulAut W)) → ∀ l ∈ L, n * l = l * n)
    {k : MulAut W} (hk : k ∈ A)
    (hkN : ∀ g ∈ A, k ∈ normalizer
      ((L.map (MulAut.conj g).toMonoidHom : Subgroup (MulAut W)) : Set (MulAut W)))
    {m : ℕ} (hm : Nat.Coprime m p) (hkm : k ^ m = 1) : k = 1 := by
  haveI : IsCyclic ↥L := hLp.1
  obtain ⟨e, he⟩ := IsCyclic.exists_generator (α := ↥L)
  let eW : MulAut W := e
  have hLgen : Subgroup.zpowers eW = L := by
    apply le_antisymm
    · rw [Subgroup.zpowers_le]; exact e.2
    · intro l hl
      have hmem : (⟨l, hl⟩ : ↥L) ∈ Subgroup.zpowers e := he ⟨l, hl⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
        have h := congrArg (Subtype.val) hn
        simpa [eW] using h⟩
  have he_order : orderOf eW = p := by
    have h1 : orderOf e = p := by
      rw [orderOf_eq_card_of_forall_mem_zpowers he, hLp.2]
    change orderOf (e : MulAut W) = p
    rw [Subgroup.orderOf_coe e]
    exact h1
  have heU : ∀ u ∈ commSub (⊤ : Subgroup W) L, eW u ∈ commSub (⊤ : Subgroup W) L :=
    commSub_top_stable151b (X := L) (g := eW)
      (fun x hx => L.mul_mem (L.mul_mem e.2 hx) (L.inv_mem e.2))
  have hfixe : ∀ u ∈ commSub (⊤ : Subgroup W) L, eW u = u → u = 1 := by
    intro u hu heu
    have hmemfix : u ∈ fixV L := by
      intro l hl
      have hl' : l ∈ Subgroup.zpowers eW := by rw [hLgen]; exact hl
      have hzu : u ∈ fixV (Subgroup.zpowers eW) := by
        rw [mem_fixV_zpowers_iff_apply]; exact heu
      exact (mem_fixV.mp hzu) l hl'
    have hmem : u ∈ commSub (⊤ : Subgroup W) L ⊓ fixV L := ⟨hu, hmemfix⟩
    rw [hfix, Subgroup.mem_bot] at hmem
    exact hmem
  have hk'_N : ∀ a ∈ A, a⁻¹ * k * a ∈ normalizer (L : Set (MulAut W)) :=
    fun a ha => s16h_mem_normalizer_conj (hkN a ha)
  have hk'_fix : ∀ a ∈ A, ∀ u ∈ commSub (⊤ : Subgroup W) L, (a⁻¹ * k * a) u = u := by
    intro a ha u hu
    have hk'A : a⁻¹ * k * a ∈ A := A.mul_mem (A.mul_mem (A.inv_mem ha) hk) ha
    have hcent : ∀ l ∈ L, (a⁻¹ * k * a) * l = l * (a⁻¹ * k * a) :=
      hχ _ hk'A (hk'_N a ha)
    have hce' : (a⁻¹ * k * a) * eW = eW * (a⁻¹ * k * a) := hcent eW e.2
    have hcU' : ∀ u ∈ commSub (⊤ : Subgroup W) L,
        (a⁻¹ * k * a) u ∈ commSub (⊤ : Subgroup W) L :=
      commSub_top_stable151b (X := L) (g := a⁻¹ * k * a)
        (fun x hx => (Subgroup.mem_normalizer_iff.mp (hk'_N a ha) x).mp hx)
    have hkm' : (a⁻¹ * k * a) ^ m = 1 := by
      have h1 : a⁻¹ * k * a = MulAut.conj a⁻¹ k := by simp [MulAut.conj_apply]
      rw [h1, ← map_pow (MulAut.conj a⁻¹) k m, hkm, map_one]
    exact s16h_fixes_of_commute_coprime hp he_order hU heU hfixe hcU' hce' hm hkm' u hu
  have hfix_map : ∀ a ∈ A, ∀ x ∈ (commSub (⊤ : Subgroup W) L).map a.toMonoidHom, k x = x := by
    intro a ha x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have hka : k * a = a * (a⁻¹ * k * a) := by group
    calc k (a u) = (k * a) u := rfl
      _ = (a * (a⁻¹ * k * a)) u := by rw [hka]
      _ = a ((a⁻¹ * k * a) u) := rfl
      _ = a u := by rw [hk'_fix a ha u hu]
  have hle : (⨆ X ∈ conjSubs A (commSub (⊤ : Subgroup W) L), X) ≤
      fixV (Subgroup.zpowers k) := by
    apply iSup_le
    intro X
    apply iSup_le
    intro hX
    obtain ⟨a, ha, rfl⟩ := hX
    intro x hx
    rw [mem_fixV_zpowers_iff_apply]
    exact hfix_map a ha x hx
  have hF : fixV (Subgroup.zpowers k) = ⊤ := top_le_iff.mp (hgen ▸ hle)
  refine MulEquiv.ext (fun v => ?_)
  have hv : v ∈ fixV (Subgroup.zpowers k) := by rw [hF]; trivial
  have hv' := mem_fixV_zpowers_iff_apply.mp hv
  simpa using hv'

theorem s16h_pRank_le_ncard_div {A : Type} [Group A] [Finite A] {Mb Lb : Subgroup A} {q : ℕ}
    (hq : q.Prime)
    (hker : ∀ k ∈ Mb, (∀ g ∈ Mb, k ∈ normalizer
        ((Lb.map (MulAut.conj g).toMonoidHom : Subgroup A) : Set A)) →
      (∃ n : ℕ, k ^ (q ^ n) = 1) → k = 1) :
    CFSG.Open.pRank q Mb ≤
      Set.ncard {X : Subgroup A | ∃ g ∈ Mb, X = Lb.map (MulAut.conj g).toMonoidHom} / q := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let S : Set (Subgroup A) :=
    {X : Subgroup A | ∃ g ∈ Mb, X = Lb.map (MulAut.conj g).toMonoidHom}
  change CFSG.Open.pRank q Mb ≤ Set.ncard S / q
  haveI : Fintype ↥S := Fintype.ofFinite _
  have hcardS : Fintype.card ↥S = Set.ncard S := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hS_mem : ∀ (g : A), g ∈ Mb → ∀ X ∈ S, X.map (MulAut.conj g).toMonoidHom ∈ S := by
    intro g hg X hX
    obtain ⟨m, hm, rfl⟩ := hX
    refine ⟨g * m, Mb.mul_mem hg hm, ?_⟩
    rw [Subgroup.map_map]
    congr 1
    ext x
    change g * (m * x * m⁻¹) * g⁻¹ = (g * m) * x * (g * m)⁻¹
    group
  letI : MulAction ↥Mb ↥S :=
    { smul := fun g X =>
        ⟨X.1.map (MulAut.conj (g : A)).toMonoidHom, hS_mem (g : A) g.2 X.1 X.2⟩
      one_smul := by
        intro X
        apply Subtype.ext
        change X.1.map (MulAut.conj ((1 : ↥Mb) : A)).toMonoidHom = X.1
        rw [Subgroup.coe_one, show MulAut.conj (1 : A) = 1 from map_one _]
        have h1 : (1 : MulAut A).toMonoidHom = MonoidHom.id A := by
          ext x
          rfl
        rw [h1, Subgroup.map_id]
      mul_smul := by
        intro g h X
        apply Subtype.ext
        change X.1.map (MulAut.conj ((g * h : ↥Mb) : A)).toMonoidHom =
          (X.1.map (MulAut.conj (h : A)).toMonoidHom).map (MulAut.conj (g : A)).toMonoidHom
        rw [Subgroup.coe_mul, Subgroup.map_map]
        congr 1
        ext x
        change (MulAut.conj ((g : A) * (h : A))) x =
          (MulAut.conj (g : A)) ((MulAut.conj (h : A)) x)
        rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
        group }
  let φ : ↥Mb →* Equiv.Perm ↥S := MulAction.toPermHom ↥Mb ↥S
  have hφ_apply : ∀ (g : ↥Mb) (X : ↥S), φ g X = g • X := fun _ _ => rfl
  have hker_triv : ∀ E : Subgroup A, E ≤ Mb → IsElemAbelian q E →
      ∀ x ∈ E.subgroupOf Mb, φ x = 1 → x = 1 := by
    intro E hE hEab x hxE₀ hφx
    have hxE : (x : A) ∈ E := Subgroup.mem_subgroupOf.mp hxE₀
    have hqpow : ∃ n : ℕ, (x : A) ^ (q ^ n) = 1 := ⟨1, by simpa using hEab.2 (x : A) hxE⟩
    have hnormalize : ∀ g ∈ Mb, (x : A) ∈ normalizer
        ((Lb.map (MulAut.conj g).toMonoidHom : Subgroup A) : Set A) := by
      intro g hg
      have hX : Lb.map (MulAut.conj g).toMonoidHom ∈ S := ⟨g, hg, rfl⟩
      have hsmul : x • (⟨Lb.map (MulAut.conj g).toMonoidHom, hX⟩ : ↥S) =
          (⟨Lb.map (MulAut.conj g).toMonoidHom, hX⟩ : ↥S) := by
        have h1 : φ x (⟨Lb.map (MulAut.conj g).toMonoidHom, hX⟩ : ↥S) =
            (⟨Lb.map (MulAut.conj g).toMonoidHom, hX⟩ : ↥S) := by rw [hφx]; rfl
        rwa [hφ_apply] at h1
      have hfix : (Lb.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj (x : A)).toMonoidHom = Lb.map (MulAut.conj g).toMonoidHom := by
        show (x • (⟨Lb.map (MulAut.conj g).toMonoidHom, hX⟩ : ↥S)).1 =
          (⟨Lb.map (MulAut.conj g).toMonoidHom, hX⟩ : ↥S).1
        rw [hsmul]
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hfix
    have hx1 : (x : A) = 1 := hker (x : A) x.2 hnormalize hqpow
    exact Subtype.ext hx1
  have hbound : ∀ E : Subgroup A, E ≤ Mb → IsElemAbelian q E →
      Nat.card E ≤ q ^ (Fintype.card ↥S / q) := by
    intro E hE hEab
    haveI : IsMulCommutative E := hEab.1
    let E₀ : Subgroup ↥Mb := E.subgroupOf Mb
    have hcardE₀ : Nat.card E₀ = Nat.card E := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hE,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective Mb)]
    have hinj : Set.InjOn φ (E₀ : Set ↥Mb) := by
      intro a ha b hb hab
      have hmem : a * b⁻¹ ∈ E₀ := E₀.mul_mem ha (E₀.inv_mem hb)
      have h1 : φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
      have h2 := hker_triv E hE hEab (a * b⁻¹) hmem h1
      rwa [mul_inv_eq_one] at h2
    have hcardE' : Nat.card (E₀.map φ) = Nat.card E₀ := by
      let φE : ↥E₀ →* Equiv.Perm ↥S := φ.comp E₀.subtype
      have hφEinj : Function.Injective φE := by
        intro a b hab
        exact Subtype.ext
          (hinj (x₁ := (a : ↥Mb)) (x₂ := (b : ↥Mb)) a.2 b.2 (by simpa [φE] using hab))
      have hmapE : (⊤ : Subgroup ↥E₀).map φE = E₀.map φ := by
        rw [show φE = φ.comp E₀.subtype from rfl, ← Subgroup.map_map, Subgroup.map_top,
          Subgroup.range_subtype]
      rw [← hmapE, Subgroup.card_map_of_injective hφEinj, Subgroup.card_top]
    have hEp : IsPGroup q E := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro x
      refine ⟨1, ?_⟩
      rw [pow_one]
      exact Subtype.ext (by simpa using hEab.2 x.1 x.2)
    have hE₀p : IsPGroup q E₀ := by
      change IsPGroup q (E.subgroupOf Mb)
      exact hEp.comap_of_injective (Subgroup.subtype Mb) (Subgroup.subtype_injective Mb)
    have hE'p : IsPGroup q (E₀.map φ) := hE₀p.map φ
    have hE'comm : ∀ x ∈ E₀.map φ, ∀ y ∈ E₀.map φ, x * y = y * x := by
      intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact congrArg (fun z : E => (z : A))
        (mul_comm' (⟨a.1, Subgroup.mem_subgroupOf.mp ha⟩ : E)
          ⟨b.1, Subgroup.mem_subgroupOf.mp hb⟩)
    have hle := CFSG.AGLEmbedding.card_le_pow_div_of_commute (E₀.map φ) hE'comm hE'p
    rw [hcardE', hcardE₀] at hle
    exact hle
  have hmain : CFSG.Open.pRank q Mb ≤ Fintype.card ↥S / q :=
    CFSG.SectionRank.pRank_le hq.one_lt (fun E hE hEab => hbound E hE hEab)
  rwa [hcardS] at hmain

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
