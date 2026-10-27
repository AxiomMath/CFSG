module

public import CFSG.Quasithin.H13.AS91Sec3Orbit
public import Certificates.Certificate89014
public import CFSG.Quasithin.H13.AS91Sec3Transport

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

@[expose] def Ten310 (l m π : Finset (Finset (Fin 24))) : Prop :=
  ∀ y, y ∈ m → y ∈ octsOf π →
    (∀ k, IsTrio k → TrioIn k π → (Coplanar m k ↔ y ∈ k) ∧ (y ∈ k → Delta m k 1)) ∧
    {k | IsTrio k ∧ TrioIn k π ∧ y ∈ k}.ncard = 3 ∧
    ∃ k₀, IsTrio k₀ ∧ TrioIn k₀ π ∧ y ∈ k₀ ∧ Delta l k₀ 1 ∧
      ∀ k, IsTrio k → TrioIn k π → y ∈ k → k ≠ k₀ → Delta l k 2

@[expose] def Master310 (l m : Finset (Finset (Fin 24))) : Prop :=
  (∃! π, IsSextet π ∧ TrioIn l π ∧ Kappa π m 1) ∧
  (∃! π', IsSextet π' ∧ TrioIn m π' ∧ Kappa π' l 1) ∧
  (∀ k, IsTrio k → Coplanar l k → Coplanar m k →
    (∃ π, IsSextet π ∧ TrioIn l π ∧ Kappa π m 1 ∧ TrioIn k π) ∨
      ∃ π', IsSextet π' ∧ TrioIn m π' ∧ Kappa π' l 1 ∧ TrioIn k π') ∧
  ∀ π, IsSextet π → TrioIn l π → Kappa π m 1 → Ten310 l m π

theorem ten310_smul {g : S24} (hg : g ∈ M24g) {l m π : Finset (Finset (Fin 24))}
    (h : Ten310 l m π) : Ten310 (g • l) (g • m) (g • π) := by
  intro y hym hyπ
  obtain ⟨y, rfl⟩ := MulAction.surjective g y
  rw [Finset.smul_mem_smul_finset_iff] at hym
  rw [octsOf_smul, Finset.smul_mem_smul_finset_iff] at hyπ
  obtain ⟨h4, h5, k₀, hk₀, hk₀π, hyk₀, hk₀l, hk₀u⟩ := h y hym hyπ
  refine ⟨fun k hk hkπ => ?_, ?_, g • k₀, (isTrio_smul_iff hg).2 hk₀, (trioIn_smul_iff g).2 hk₀π,
    Finset.smul_mem_smul_finset hyk₀, (delta_smul_iff hg 1).2 hk₀l, fun k hk hkπ hyk hne => ?_⟩
  · obtain ⟨k, rfl⟩ := MulAction.surjective g k
    rw [isTrio_smul_iff hg] at hk
    rw [trioIn_smul_iff g] at hkπ
    rw [coplanar_smul_iff hg, Finset.smul_mem_smul_finset_iff, delta_smul_iff hg 1]
    exact h4 k hk hkπ
  · have himg : {k | IsTrio k ∧ TrioIn k (g • π) ∧ g • y ∈ k} =
        (fun k => g • k) '' {k | IsTrio k ∧ TrioIn k π ∧ y ∈ k} := by
      ext k
      constructor
      · rintro ⟨hk, hkπ, hyk⟩
        obtain ⟨k, rfl⟩ := MulAction.surjective g k
        exact ⟨k, ⟨(isTrio_smul_iff hg).1 hk, (trioIn_smul_iff g).1 hkπ,
          (Finset.smul_mem_smul_finset_iff g).1 hyk⟩, rfl⟩
      · rintro ⟨k, ⟨hk, hkπ, hyk⟩, rfl⟩
        exact ⟨(isTrio_smul_iff hg).2 hk, (trioIn_smul_iff g).2 hkπ,
          Finset.smul_mem_smul_finset hyk⟩
    rw [himg, Set.ncard_image_of_injective _ (MulAction.injective g)]
    exact h5
  · obtain ⟨k, rfl⟩ := MulAction.surjective g k
    rw [isTrio_smul_iff hg] at hk
    rw [trioIn_smul_iff g] at hkπ
    rw [Finset.smul_mem_smul_finset_iff] at hyk
    rw [delta_smul_iff hg 2]
    exact hk₀u k hk hkπ hyk fun e => hne (by rw [e])

theorem master310_smul {g : S24} (hg : g ∈ M24g) {l m : Finset (Finset (Fin 24))}
    (h : Master310 l m) : Master310 (g • l) (g • m) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (MulAction.bijective g).existsUnique_iff.2 ((existsUnique_congr fun x => ?_).2 h1)
    exact and_congr (isSextet_smul_iff hg) (and_congr (trioIn_smul_iff g) (kappa_smul_iff hg 1))
  · refine (MulAction.bijective g).existsUnique_iff.2 ((existsUnique_congr fun x => ?_).2 h2)
    exact and_congr (isSextet_smul_iff hg) (and_congr (trioIn_smul_iff g) (kappa_smul_iff hg 1))
  · intro k hk hkl hkm
    obtain ⟨k, rfl⟩ := MulAction.surjective g k
    rw [coplanar_smul_iff hg] at hkl hkm
    rcases h3 k ((isTrio_smul_iff hg).1 hk) hkl hkm with ⟨π, hπ, hlπ, hmπ, hkπ⟩ |
        ⟨π, hπ, hmπ, hlπ, hkπ⟩
    · exact Or.inl ⟨g • π, (isSextet_smul_iff hg).2 hπ, (trioIn_smul_iff g).2 hlπ,
        (kappa_smul_iff hg 1).2 hmπ, (trioIn_smul_iff g).2 hkπ⟩
    · exact Or.inr ⟨g • π, (isSextet_smul_iff hg).2 hπ, (trioIn_smul_iff g).2 hmπ,
        (kappa_smul_iff hg 1).2 hlπ, (trioIn_smul_iff g).2 hkπ⟩
  · intro π hπ hlπ hmπ
    obtain ⟨π, rfl⟩ := MulAction.surjective g π
    exact ten310_smul hg (h4 π ((isSextet_smul_iff hg).1 hπ) ((trioIn_smul_iff g).1 hlπ)
      ((kappa_smul_iff hg 1).1 hmπ))

theorem piCheck_spec {Ts : Array (List ℕ)} {l m : ℕ} (h : Native.piCheck Ts l m = true) :
    ∃ π π' xy : ℕ, (Ts[l]!.filter fun q => Native.oneIn m q) = [π] ∧
      (Ts[m]!.filter fun q => Native.oneIn l q) = [π'] ∧
      (∀ k < 3795, Native.coplanar Ts l k = true → Native.coplanar Ts m k = true →
        π ∈ Ts[k]! ∨ π' ∈ Ts[k]!) ∧
      (∀ k < 3795, (π ∈ Ts[k]! ∧ Native.octIn m π ∈ Native.octsT (Native.trioList ())[k]!) ↔
        (Native.coplanar Ts l k = true ∧ Native.coplanar Ts m k = true ∧ π ∈ Ts[k]!)) ∧
      ((List.range 3795).filter fun k => Ts[k]!.contains π &&
        (Native.octsT (Native.trioList ())[k]!).contains (Native.octIn m π)).length = 3 ∧
      (∀ k < 3795, π ∈ Ts[k]! → Native.octIn m π ∈ Native.octsT (Native.trioList ())[k]! →
        k ≠ m ∧ Native.meets (Native.trioList ())[m]! (Native.trioList ())[k]! = true) ∧
      xy < 3795 ∧ (π ∈ Ts[xy]! ∧ Native.octIn m π ∈ Native.octsT (Native.trioList ())[xy]!) ∧
      xy ≠ l ∧ Native.meets (Native.trioList ())[l]! (Native.trioList ())[xy]! = true ∧
      (∀ k < 3795, π ∈ Ts[k]! → Native.octIn m π ∈ Native.octsT (Native.trioList ())[k]! →
        k ≠ xy → Native.meets (Native.trioList ())[l]! (Native.trioList ())[k]! = false ∧
          Native.coplanar Ts l k = true) := by
  unfold Native.piCheck at h
  split at h
  · rename_i π π' hπ hπ'
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, -⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
    set Y := Native.octIn m π
    set xy := Native.trioIdx (Native.sort3 (Native.octIn l π') Y
      (Native.full ^^^ Native.octIn l π' ^^^ Y))
    set pen := List.filter (fun k => Ts[k]!.contains π &&
      (Native.octsT Native.trioList[k]!).contains Y) (List.range Native.nTrio) with hpen_def
    set co := List.filter (fun k => Native.coplanar Ts l k && Native.coplanar Ts m k)
      (List.range Native.nTrio) with hco_def
    set cop := List.filter (fun k => Ts[k]!.contains π) co with hcop_def
    have hmem_pen : ∀ k, k ∈ pen ↔
        k < 3795 ∧ π ∈ Ts[k]! ∧ Y ∈ Native.octsT Native.trioList[k]! := by
      intro k
      simp only [hpen_def, List.mem_filter, List.mem_range, Bool.and_eq_true,
        List.contains_eq_mem, decide_eq_true_eq]
      exact Iff.rfl
    have hmem_co : ∀ k, k ∈ co ↔
        k < 3795 ∧ Native.coplanar Ts l k = true ∧ Native.coplanar Ts m k = true := by
      intro k
      simp only [hco_def, List.mem_filter, List.mem_range, Bool.and_eq_true]
      exact Iff.rfl
    have hmem_cop : ∀ k, k ∈ cop ↔ (k < 3795 ∧ Native.coplanar Ts l k = true ∧
        Native.coplanar Ts m k = true) ∧ π ∈ Ts[k]! := by
      intro k
      simp only [hcop_def, List.mem_filter, List.contains_eq_mem, decide_eq_true_eq, hmem_co]
    have hsub : cop ⊆ pen := fun x hx => by
      have := h3 x hx
      rwa [List.contains_eq_mem, decide_eq_true_eq] at this
    have hlen_pen : pen.length = 3 := by simpa using h4
    have hlen_cop : cop.length = 3 := by simpa using h2
    have hnd : cop.Nodup := (List.nodup_range.filter _).filter _
    have hperm : cop.Perm pen :=
      (hnd.subperm hsub).perm_of_length_le (by rw [hlen_pen, hlen_cop])
    refine ⟨π, π', xy, hπ, hπ', ?_, ?_, hlen_pen, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk hl hm
      have := h1 k ((hmem_co k).2 ⟨hk, hl, hm⟩)
      simpa [Bool.or_eq_true, List.contains_eq_mem] using this
    · intro k hk
      constructor
      · rintro ⟨hπk, hYk⟩
        have := (hmem_cop k).1 (hperm.mem_iff.2 ((hmem_pen k).2 ⟨hk, hπk, hYk⟩))
        exact ⟨this.1.2.1, this.1.2.2, this.2⟩
      · rintro ⟨hl, hm, hπk⟩
        have := (hmem_pen k).1 (hsub ((hmem_cop k).2 ⟨⟨hk, hl, hm⟩, hπk⟩))
        exact ⟨this.2.1, this.2.2⟩
    · intro k hk hπk hYk
      have := h5 k ((hmem_pen k).2 ⟨hk, hπk, hYk⟩)
      exact ⟨by simpa using this.1, this.2⟩
    · exact of_decide_eq_true h7
    · have := h8
      rw [List.contains_eq_mem, decide_eq_true_eq] at this
      exact ((hmem_pen xy).1 this).2
    · simpa using h9
    · exact h10
    · intro k hk hπk hYk hne
      have := h11 k ((hmem_pen k).2 ⟨hk, hπk, hYk⟩)
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at this
      rcases this with h | h
      · exact absurd h hne
      · exact h
  · exact absurd h (by simp)

theorem octIn_spec {p q : ℕ} (h : Native.oneIn p q = true) {o : ℕ} :
    (o ∈ Native.octsT (Native.trioList ())[p]! ∧ o ∈ Native.octsS (Native.sextList ())[q]!) ↔
      o = Native.octIn p q := by
  have e : ((Native.octsT (Native.trioList ())[p]!).filter fun o =>
      (Native.octsS (Native.sextList ())[q]!).contains o) = [Native.octIn p q] := by
    simp only [Native.oneIn, beq_iff_eq, List.length_eq_one_iff] at h
    obtain ⟨Y, hY⟩ := h
    simp only [Native.octIn, hY, List.headD_cons]
  rw [← List.mem_singleton, ← e, List.mem_filter, List.contains_eq_mem, decide_eq_true_eq]

section Cert


theorem eq_maskFin_octIn {p q : ℕ} (hp : p < 3795) (hq : q < 1771) (h : Native.oneIn p q = true)
    {y : Finset (Fin 24)} (hym : y ∈ trioFin p) (hyπ : y ∈ octsOf (sextFin q)) :
    y = maskFin (Native.octIn p q) := by
  rw [trioFin_eq_toFinset, List.mem_toFinset, List.mem_map] at hym
  obtain ⟨o, ho, rfl⟩ := hym
  rw [maskFin_mem_octsOf_sextFin hq (octsT_lt hp o ho)] at hyπ
  rw [(octIn_spec h).1 ⟨ho, hyπ⟩]

theorem sextet_of_oneIn_filter {a b q : ℕ} (ha : a < 3795) (hb : b < 3795)
    (h : ((Native.trioSexts ())[a]!.filter fun q => Native.oneIn b q) = [q]) :
    q < 1771 ∧ TrioIn (trioFin a) (sextFin q) ∧ Kappa (sextFin q) (trioFin b) 1 ∧
      ∀ π, IsSextet π → TrioIn (trioFin a) π → Kappa π (trioFin b) 1 → π = sextFin q := by
  have hmem : q ∈ (Native.trioSexts ())[a]!.filter fun q => Native.oneIn b q := by
    rw [h]
    exact List.mem_singleton_self q
  rw [List.mem_filter] at hmem
  obtain ⟨h1, h2⟩ := hmem
  obtain ⟨hq, h3⟩ := (mem_trioSexts ha).1 h1
  refine ⟨hq, h3, (oneIn_iff hb hq).1 (by simpa using h2), ?_⟩
  intro π hπ hlπ hkπ
  obtain ⟨q₁, hq₁, rfl⟩ := (isSextet_iff π).1 hπ
  have : q₁ ∈ (Native.trioSexts ())[a]!.filter fun q => Native.oneIn b q :=
    List.mem_filter.2 ⟨(mem_trioSexts ha).2 ⟨hq₁, hlπ⟩, (oneIn_iff hb hq₁).2 hkπ⟩
  rw [h, List.mem_singleton] at this
  rw [this]

theorem ten310_base {p π : ℕ} (hp : p < 3795)
    (h : Native.piCheck (Native.trioSexts ()) 0 p = true)
    (hπ : ((Native.trioSexts ())[0]!.filter fun q => Native.oneIn p q) = [π]) :
    Ten310 (trioFin 0) (trioFin p) (sextFin π) := by
  obtain ⟨π₁, -, xy, hπ₁, -, -, hS2, hlen, hS4, hxy, hxy1, hxy2, hxy3, hS6⟩ := piCheck_spec h
  obtain rfl : π = π₁ := by simpa using hπ.symm.trans hπ₁
  have h0 : (0 : ℕ) < 3795 := by norm_num
  obtain ⟨hq, hlπ, hkπ, -⟩ := sextet_of_oneIn_filter h0 hp hπ
  have hone : Native.oneIn p π = true := (oneIn_iff hp hq).2 hkπ
  have hYlt : Native.octIn p π < 2 ^ 24 := octsT_lt hp _ ((octIn_spec hone).2 rfl).1
  have hmY : ∀ {k : ℕ}, k < 3795 → (maskFin (Native.octIn p π) ∈ trioFin k ↔
      Native.octIn p π ∈ Native.octsT (Native.trioList ())[k]!) :=
    fun hk => maskFin_mem_trioFin hk hYlt
  intro y hym hyπ
  obtain rfl := eq_maskFin_octIn hp hq hone hym hyπ
  refine ⟨fun k hk hkπ => ?_, ?_, trioFin xy, isTrio_trioFin hxy,
    ((mem_trioSexts hxy).1 hxy1.1).2, (hmY hxy).2 hxy1.2, ?_, fun k hk hkπ hyk hne => ?_⟩
  · obtain ⟨k₁, hk₁, rfl⟩ := (isTrio_iff k).1 hk
    have hπk : π ∈ (Native.trioSexts ())[k₁]! := (mem_trioSexts hk₁).2 ⟨hq, hkπ⟩
    refine ⟨⟨fun hcop => ?_, fun hy => ?_⟩, fun hy => ?_⟩
    · have hlk : Coplanar (trioFin 0) (trioFin k₁) :=
        ⟨sextFin π, isSextet_sextFin hq, hlπ, hkπ⟩
      exact (hmY hk₁).2 ((hS2 k₁ hk₁).2 ⟨(coplanar_iff h0 hk₁).2 hlk,
        (coplanar_iff hp hk₁).2 hcop, hπk⟩).2
    · exact (coplanar_iff hp hk₁).1 ((hS2 k₁ hk₁).1 ⟨hπk, (hmY hk₁).1 hy⟩).2.1
    · have h5 := hS4 k₁ hk₁ hπk ((hmY hk₁).1 hy)
      exact ⟨fun e => h5.1 (trioFin_injective hk₁ hp e), (meets_iff hp hk₁).1 h5.2⟩
  · refine (ncard_eq_length_filter (F := trioFin) (n := 3795)
      (fun a ha b hb e => trioFin_injective ha hb e) isTrio_iff
      (fun k => (Native.trioSexts ())[k]!.contains π &&
        (Native.octsT (Native.trioList ())[k]!).contains (Native.octIn p π))
      (Q := fun k => TrioIn k (sextFin π) ∧ maskFin (Native.octIn p π) ∈ k) ?_).trans hlen
    intro k hk
    rw [Bool.and_eq_true, List.contains_eq_mem, List.contains_eq_mem, decide_eq_true_eq,
      decide_eq_true_eq, hmY hk, mem_trioSexts hk]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨hq, h1⟩, h2⟩, fun ⟨⟨_, h1⟩, h2⟩ => ⟨h1, h2⟩⟩
  · exact ⟨fun e => hxy2 (trioFin_injective hxy h0 e), (meets_iff h0 hxy).1 hxy3⟩
  · obtain ⟨k₁, hk₁, rfl⟩ := (isTrio_iff k).1 hk
    have hπk : π ∈ (Native.trioSexts ())[k₁]! := (mem_trioSexts hk₁).2 ⟨hq, hkπ⟩
    have h6 := hS6 k₁ hk₁ hπk ((hmY hk₁).1 hyk) fun e => hne (by rw [e])
    refine ⟨?_, (coplanar_iff h0 hk₁).1 h6.2⟩
    by_contra hnd
    have := (meets_iff h0 hk₁).2 hnd
    rw [h6.1] at this
    exact Bool.false_ne_true this


theorem piCheck_base {p : ℕ} (hp : p < 3795) (hd : Delta (trioFin 0) (trioFin p) 3) :
    Native.piCheck (Native.trioSexts ()) 0 p = true := by
  have h : Native.stmt310Check () = true := Certificates.certificate89014
  simp only [Native.stmt310Check, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at h
  rcases h p hp with h1 | h1
  · exact absurd ((zc_eq (by norm_num) hp).trans hd) h1
  · exact h1

theorem master310_base {p : ℕ} (hp : p < 3795) (hd : Delta (trioFin 0) (trioFin p) 3) :
    Master310 (trioFin 0) (trioFin p) := by
  have h0 : (0 : ℕ) < 3795 := by norm_num
  have hpi := piCheck_base hp hd
  obtain ⟨π, π', -, hπ, hπ', hS1, -⟩ := piCheck_spec hpi
  obtain ⟨hq, hlπ, hkπ, huniq⟩ := sextet_of_oneIn_filter h0 hp hπ
  obtain ⟨hq', hmπ', hlπ', huniq'⟩ := sextet_of_oneIn_filter hp h0 hπ'
  refine ⟨⟨sextFin π, ⟨isSextet_sextFin hq, hlπ, hkπ⟩, fun x hx => huniq x hx.1 hx.2.1 hx.2.2⟩,
    ⟨sextFin π', ⟨isSextet_sextFin hq', hmπ', hlπ'⟩, fun x hx => huniq' x hx.1 hx.2.1 hx.2.2⟩,
    ?_, ?_⟩
  · intro k hk hkl hkm
    obtain ⟨k₁, hk₁, rfl⟩ := (isTrio_iff k).1 hk
    rcases hS1 k₁ hk₁ ((coplanar_iff h0 hk₁).2 hkl) ((coplanar_iff hp hk₁).2 hkm) with h | h
    · exact Or.inl ⟨sextFin π, isSextet_sextFin hq, hlπ, hkπ, ((mem_trioSexts hk₁).1 h).2⟩
    · exact Or.inr ⟨sextFin π', isSextet_sextFin hq', hmπ', hlπ', ((mem_trioSexts hk₁).1 h).2⟩
  · intro π₁ hπ₁ h1 h2
    obtain rfl := huniq π₁ hπ₁ h1 h2
    exact ten310_base hp hpi hπ

theorem master310 {l m : Finset (Finset (Fin 24))} (hl : IsTrio l) (hm : IsTrio m)
    (h : Delta l m 3) : Master310 l m := by
  refine forall_trio_of_base (P := fun l => ∀ m, IsTrio m → Delta l m 3 → Master310 l m) ?_ ?_
    hl m hm h
  · intro g hg l hP m hm hd
    obtain ⟨m, rfl⟩ := MulAction.surjective g m
    exact master310_smul hg (hP m ((isTrio_smul_iff hg).1 hm) ((delta_smul_iff hg 3).1 hd))
  · intro m hm hd
    obtain ⟨p, hp, rfl⟩ := (isTrio_iff m).1 hm
    exact master310_base hp hd

theorem existsUnique_sextet_kappa_one {l m : Finset (Finset (Fin 24))} (hl : IsTrio l)
    (hm : IsTrio m) (h : Delta l m 3) : ∃! π, IsSextet π ∧ TrioIn l π ∧ Kappa π m 1 :=
  (master310 hl hm h).1

theorem existsUnique_sextet_kappa_one' {l m : Finset (Finset (Fin 24))} (hl : IsTrio l)
    (hm : IsTrio m) (h : Delta l m 3) : ∃! π', IsSextet π' ∧ TrioIn m π' ∧ Kappa π' l 1 :=
  (master310 hl hm h).2.1

theorem trioIn_or_trioIn_of_coplanar {l m π π' k : Finset (Finset (Fin 24))} (hl : IsTrio l)
    (hm : IsTrio m) (h : Delta l m 3) (hπ : IsSextet π) (hlπ : TrioIn l π) (hmπ : Kappa π m 1)
    (hπ' : IsSextet π') (hmπ' : TrioIn m π') (hlπ' : Kappa π' l 1) (hk : IsTrio k)
    (hkl : Coplanar l k) (hkm : Coplanar m k) : TrioIn k π ∨ TrioIn k π' := by
  obtain ⟨h1, h2, h3, -⟩ := master310 hl hm h
  rcases h3 k hk hkl hkm with ⟨σ, hσ, hlσ, hmσ, hkσ⟩ | ⟨σ, hσ, hmσ, hlσ, hkσ⟩
  · exact Or.inl (h1.unique ⟨hσ, hlσ, hmσ⟩ ⟨hπ, hlπ, hmπ⟩ ▸ hkσ)
  · exact Or.inr (h2.unique ⟨hσ, hmσ, hlσ⟩ ⟨hπ', hmπ', hlπ'⟩ ▸ hkσ)

theorem coplanar_iff_mem_of_trioIn {l m π k : Finset (Finset (Fin 24))} {y : Finset (Fin 24)}
    (hl : IsTrio l) (hm : IsTrio m) (h : Delta l m 3) (hπ : IsSextet π) (hlπ : TrioIn l π)
    (hmπ : Kappa π m 1) (hym : y ∈ m) (hyπ : y ∈ octsOf π) (hk : IsTrio k) (hkπ : TrioIn k π) :
    (Coplanar m k ↔ y ∈ k) ∧ (y ∈ k → Delta m k 1) :=
  ((master310 hl hm h).2.2.2 π hπ hlπ hmπ y hym hyπ).1 k hk hkπ

theorem ncard_trioIn_mem {l m π : Finset (Finset (Fin 24))} {y : Finset (Fin 24)}
    (hl : IsTrio l) (hm : IsTrio m) (h : Delta l m 3) (hπ : IsSextet π) (hlπ : TrioIn l π)
    (hmπ : Kappa π m 1) (hym : y ∈ m) (hyπ : y ∈ octsOf π) :
    {k | IsTrio k ∧ TrioIn k π ∧ y ∈ k}.ncard = 3 :=
  ((master310 hl hm h).2.2.2 π hπ hlπ hmπ y hym hyπ).2.1

theorem exists_delta_one_trioIn {l m π : Finset (Finset (Fin 24))} {y : Finset (Fin 24)}
    (hl : IsTrio l) (hm : IsTrio m) (h : Delta l m 3) (hπ : IsSextet π) (hlπ : TrioIn l π)
    (hmπ : Kappa π m 1) (hym : y ∈ m) (hyπ : y ∈ octsOf π) :
    ∃ k₀, IsTrio k₀ ∧ TrioIn k₀ π ∧ y ∈ k₀ ∧ Delta l k₀ 1 ∧
      ∀ k, IsTrio k → TrioIn k π → y ∈ k → k ≠ k₀ → Delta l k 2 :=
  ((master310 hl hm h).2.2.2 π hπ hlπ hmπ y hym hyπ).2.2

end Cert

end CFSG.Quasithin.H13.AS91.M24G
