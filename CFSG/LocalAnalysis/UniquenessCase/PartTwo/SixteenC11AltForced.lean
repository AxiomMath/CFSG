module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11AltCrit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11AltWords

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin
open scoped Pointwise

@[expose] def S16C11AltGrp {n : ℕ} (gens : List ↥(alternatingGroup (Fin n))) :
    Subgroup ↥(alternatingGroup (Fin n)) :=
  Subgroup.closure {g | g ∈ gens}

private lemma s16c11_altforced_ncard_orbit_eq_relIndex {G : Type*} [Group G] {V : Type*}
    [CommGroup V] [Finite G] {ρ : G →* MulAut V} {T X : Subgroup G} {y : V}
    (hS : X ⊓ (MulAction.stabilizer (MulAut V) y).comap ρ = T) :
    {z : V | ∃ x ∈ X, ρ x y = z}.ncard = T.relIndex X := by
  letI : MulAction G V := MulAction.compHom V ρ
  have hstab : MulAction.stabilizer G y = (MulAction.stabilizer (MulAut V) y).comap ρ := by
    ext g
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, MulAction.compHom_smul_def]
  have horb : {z : V | ∃ x ∈ X, ρ x y = z} = MulAction.orbit ↥X y := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨(x : G), x.2, rfl⟩
  rw [horb, ← MulAction.index_stabilizer, ← MulAction.stabilizer_subgroupOf X y, hstab,
    ← Subgroup.inf_subgroupOf_left ((MulAction.stabilizer (MulAut V) y).comap ρ) X, ← hS]
  rfl

theorem s16c11_alt_grp_fixes {n : ℕ} {gens : List ↥(alternatingGroup (Fin n))}
    {y : (FFModel.altDn n).Mod} (h : ∀ g ∈ gens, S16C11AltAct n g y = y) :
    ∀ t ∈ S16C11AltGrp gens, S16C11AltAct n t y = y := by
  intro t ht
  have hle : S16C11AltGrp gens ≤
      (MulAction.stabilizer (MulAut (FFModel.altDn n).Mod) y).comap (S16C11AltAct n) := by
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    exact Subgroup.mem_comap.2 (MulAction.mem_stabilizer_iff.2 (h g hg))
  exact MulAction.mem_stabilizer_iff.1 (Subgroup.mem_comap.1 (hle ht))

theorem s16c11_alt_pgroup_of_words {n : ℕ} (gens : List ↥(alternatingGroup (Fin n))) (m e c : ℕ)
    (hfix : S16C11AltWords gens (m + 1) = S16C11AltWords gens m)
    (hcard : (S16C11AltWords gens m).card = 2 ^ e)
    (hgroup : Nat.card ↥(alternatingGroup (Fin n)) = 2 ^ e * c) (hc : ¬ 2 ∣ c) :
    IsPGroup 2 ↥(S16C11AltGrp gens) ∧ ¬ 2 ∣ (S16C11AltGrp gens).index := by
  have hT : Nat.card ↥(S16C11AltGrp gens) = 2 ^ e := by
    rw [S16C11AltGrp, s16c11_alt_card_closure gens m hfix, hcard]
  have hidx : (S16C11AltGrp gens).index = c := by
    have h := Subgroup.card_mul_index (S16C11AltGrp gens)
    rw [hT, hgroup] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos e) h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨IsPGroup.of_card hT, by rw [hidx]; exact hc⟩

theorem s16c11_alt_forced_of_checks {n : ℕ} (gens : List ↥(alternatingGroup (Fin n)))
    (ws : Finset ↥(alternatingGroup (Fin n))) (hws : ∀ t ∈ ws, t ∈ S16C11AltGrp gens)
    {x₀ xa xb : Fin n → ZMod 2} {N : ℕ} (h₀ : ∑ i, x₀ i = 0) (ha : ∑ i, xa i = 0)
    (hb : ∑ i, xb i = 0) (hne : ¬ S16C11AltEqv 0 x₀)
    (hfix : ∀ g ∈ gens, S16C11AltEqv x₀ (S16C11AltPact (g : Equiv.Perm (Fin n)) x₀))
    (horb : {z : (FFModel.altDn n).Mod | ∃ g : ↥(alternatingGroup (Fin n)),
      S16C11AltAct n g (S16C11AltCls n x₀) = z}.ncard ≤ N)
    (huniq : ∀ y : (FFModel.altDn n).Mod, y ≠ 1 →
      (∀ t ∈ S16C11AltGrp gens, S16C11AltAct n t y = y) →
      {z : (FFModel.altDn n).Mod | ∃ g : ↥(alternatingGroup (Fin n)), S16C11AltAct n g y = z}.ncard
        ≤ N → y = S16C11AltCls n x₀)
    (hab : ¬ S16C11AltEqv xa xb)
    (hpair : ∀ k : Fin (2 ^ n), S16C11AltWt (S16C11AltBits n k) = S16C11AltWt x₀ →
      ¬ S16C11AltEqv x₀ (S16C11AltBits n k) → ¬ S16C11AltEqv xa (S16C11AltBits n k) →
      ¬ S16C11AltEqv xb (S16C11AltBits n k) →
      ∃ t₁ ∈ ws, ∃ t₂ ∈ ws,
        ¬ S16C11AltEqv (S16C11AltBits n k)
          (S16C11AltPact (t₁ : Equiv.Perm (Fin n)) (S16C11AltBits n k)) ∧
        ¬ S16C11AltEqv (S16C11AltBits n k)
          (S16C11AltPact (t₂ : Equiv.Perm (Fin n)) (S16C11AltBits n k)) ∧
        ¬ S16C11AltEqv (S16C11AltPact (t₁ : Equiv.Perm (Fin n)) (S16C11AltBits n k))
          (S16C11AltPact (t₂ : Equiv.Perm (Fin n)) (S16C11AltBits n k))) :
    S16C11Forced (S16C11AltAct n) (S16C11AltGrp gens) N (S16C11AltCls n x₀) (S16C11AltCls n xa)
      (S16C11AltCls n xb) := by
  have hfixT : ∀ t ∈ S16C11AltGrp gens,
      S16C11AltAct n t (S16C11AltCls n x₀) = S16C11AltCls n x₀ :=
    s16c11_alt_grp_fixes fun g hg => (s16c11_alt_fixed_iff g h₀).mpr (hfix g hg)
  refine ⟨?_, hfixT, horb, huniq, ?_, ?_⟩
  · intro h
    exact hne ((s16c11_alt_cls_one_iff h₀).mp h)
  · intro h
    exact hab ((s16c11_alt_cls_eq_iff ha hb).mp h)
  · rintro z ⟨g, rfl⟩ hz_ne hz_orbit
    let g' : ↥(alternatingGroup (Fin n)) := g
    set v : Fin n → ZMod 2 := S16C11AltPact (g' : Equiv.Perm (Fin n)) x₀ with hv_def
    have hact : S16C11AltAct n g (S16C11AltCls n x₀) = S16C11AltCls n v := by
      rw [hv_def]
      exact s16c11_alt_act_cls g' h₀
    have hv : ∑ i, v i = 0 := by
      rw [hv_def]
      exact (s16c11_alt_sum_pact (g' : Equiv.Perm (Fin n)) x₀).trans h₀
    have hcls_ne : S16C11AltCls n v ≠ S16C11AltCls n x₀ := by
      rw [← hact]
      exact hz_ne
    have hne0 : ¬ S16C11AltEqv x₀ v := fun h =>
      hcls_ne ((s16c11_alt_cls_eq_iff h₀ hv).mpr h).symm
    have hwt : S16C11AltWt v = S16C11AltWt x₀ := by
      rw [hv_def]
      exact s16c11_alt_wt_pact (g' : Equiv.Perm (Fin n)) x₀
    by_cases hxa : S16C11AltEqv xa v
    · exact Or.inl (hact.trans ((s16c11_alt_cls_eq_iff ha hv).mpr hxa).symm)
    by_cases hxb : S16C11AltEqv xb v
    · exact Or.inr (hact.trans ((s16c11_alt_cls_eq_iff hb hv).mpr hxb).symm)
    obtain ⟨k, hk, hvk⟩ := s16c11_alt_exists_bits v
    obtain ⟨t₁, ht₁, t₂, ht₂, hc₁, hc₂, hc₃⟩ :=
      hpair ⟨k, hk⟩ (by rw [← hvk]; exact hwt) (by rw [← hvk]; exact hne0)
        (by rw [← hvk]; exact hxa) (by rw [← hvk]; exact hxb)
    have h2 := s16c11_alt_two_lt_ncard_orbit hv (hws t₁ ht₁) (hws t₂ ht₂)
      (by rw [hvk]; exact hc₁) (by rw [hvk]; exact hc₂) (by rw [hvk]; exact hc₃)
    rw [hact] at hz_orbit
    exact absurd h2 (not_lt.mpr hz_orbit)

theorem s16c11_alt_uniq_of_check_large {n : ℕ} (gens : List ↥(alternatingGroup (Fin n)))
    {x₀ : Fin n → ZMod 2} (h₀ : ∑ i, x₀ i = 0) (N : ℕ) (xs : List (Fin n → ZMod 2))
    (hxs : ∀ w ∈ xs, ∑ i, w i = 0)
    (hlarge : ∀ w ∈ xs, N < {z : (FFModel.altDn n).Mod |
      ∃ g : ↥(alternatingGroup (Fin n)), S16C11AltAct n g (S16C11AltCls n w) = z}.ncard)
    (h : ∀ k : Fin (2 ^ n), ∑ i, S16C11AltBits n k i = 0 →
      ¬ S16C11AltEqv 0 (S16C11AltBits n k) →
      (∀ g ∈ gens, S16C11AltEqv (S16C11AltBits n k)
        (S16C11AltPact (g : Equiv.Perm (Fin n)) (S16C11AltBits n k))) →
      S16C11AltEqv x₀ (S16C11AltBits n k) ∨ ∃ w ∈ xs, S16C11AltEqv w (S16C11AltBits n k)) :
    ∀ y : (FFModel.altDn n).Mod, y ≠ 1 → (∀ t ∈ S16C11AltGrp gens, S16C11AltAct n t y = y) →
      {z : (FFModel.altDn n).Mod | ∃ g : ↥(alternatingGroup (Fin n)), S16C11AltAct n g y = z}.ncard
        ≤ N → y = S16C11AltCls n x₀ := by
  intro y hyne hyfix hyorb
  obtain ⟨v, hv, rfl⟩ := s16c11_alt_cls_surjective n y
  obtain ⟨k, hk, rfl⟩ := s16c11_alt_exists_bits v
  have hne : ¬ S16C11AltEqv 0 (S16C11AltBits n k) := fun h =>
    hyne ((s16c11_alt_cls_one_iff hv).mpr h)
  have hfixg : ∀ g ∈ gens, S16C11AltEqv (S16C11AltBits n k)
      (S16C11AltPact (g : Equiv.Perm (Fin n)) (S16C11AltBits n k)) := fun g hg =>
    (s16c11_alt_fixed_iff g hv).mp (hyfix g (Subgroup.subset_closure hg))
  rcases h ⟨k, hk⟩ hv hne hfixg with heqv | ⟨w, hw, hwv⟩
  · exact ((s16c11_alt_cls_eq_iff h₀ hv).mpr heqv).symm
  · have hwsum : ∑ i, w i = 0 := hxs w hw
    have hcls : S16C11AltCls n (S16C11AltBits n k) = S16C11AltCls n w :=
      ((s16c11_alt_cls_eq_iff hwsum hv).mpr hwv).symm
    have hbig : N < {z : (FFModel.altDn n).Mod | ∃ g : ↥(alternatingGroup (Fin n)),
        S16C11AltAct n g (S16C11AltCls n (S16C11AltBits n k)) = z}.ncard := by
      rw [hcls]
      exact hlarge w hw
    exact absurd hbig (not_lt.mpr hyorb)

theorem s16c11_alt_uniq_of_check {n : ℕ} (gens : List ↥(alternatingGroup (Fin n)))
    {x₀ : Fin n → ZMod 2} (h₀ : ∑ i, x₀ i = 0) (N : ℕ)
    (h : ∀ k : Fin (2 ^ n), ∑ i, S16C11AltBits n k i = 0 →
      ¬ S16C11AltEqv 0 (S16C11AltBits n k) →
      (∀ g ∈ gens, S16C11AltEqv (S16C11AltBits n k)
        (S16C11AltPact (g : Equiv.Perm (Fin n)) (S16C11AltBits n k))) →
      S16C11AltEqv x₀ (S16C11AltBits n k)) :
    ∀ y : (FFModel.altDn n).Mod, y ≠ 1 → (∀ t ∈ S16C11AltGrp gens, S16C11AltAct n t y = y) →
      {z : (FFModel.altDn n).Mod | ∃ g : ↥(alternatingGroup (Fin n)), S16C11AltAct n g y = z}.ncard
        ≤ N → y = S16C11AltCls n x₀ :=
  s16c11_alt_uniq_of_check_large gens h₀ N [] (by simp) (by simp)
    fun k h1 h2 h3 => Or.inl (h k h1 h2 h3)

theorem s16c11_alt_stab_data_of_checks {n : ℕ} (gens : List ↥(alternatingGroup (Fin n))) (m : ℕ)
    (hfixw : S16C11AltWords gens (m + 1) = S16C11AltWords gens m)
    {x₀ xa xb : Fin n → ZMod 2} (sa sb : ↥(alternatingGroup (Fin n))) (h₀ : ∑ i, x₀ i = 0)
    (ha : ∑ i, xa i = 0) (hb : ∑ i, xb i = 0) (hxa : ¬ S16C11AltEqv x₀ xa)
    (hxb : ¬ S16C11AltEqv x₀ xb) (hab : ¬ S16C11AltEqv xa xb)
    (hfix : ∀ g ∈ gens, S16C11AltEqv x₀ (S16C11AltPact (g : Equiv.Perm (Fin n)) x₀))
    (hstab : ∀ g ∈ gens, S16C11AltTriple x₀ xa xb (g : Equiv.Perm (Fin n)))
    (hpass : ∀ g : Equiv.Perm (Fin n), S16C11AltTriple x₀ xa xb g →
      S16C11AltEqv x₀ (S16C11AltPact g x₀) → Equiv.Perm.sign g = 1 →
      g ∈ (S16C11AltWords gens m).image Subtype.val)
    (hsa : S16C11AltTriple x₀ xa xb (sa : Equiv.Perm (Fin n)))
    (hsa' : S16C11AltEqv xa (S16C11AltPact (sa : Equiv.Perm (Fin n)) x₀))
    (hsb : S16C11AltTriple x₀ xa xb (sb : Equiv.Perm (Fin n)))
    (hsb' : S16C11AltEqv xb (S16C11AltPact (sb : Equiv.Perm (Fin n)) x₀)) :
    S16C11AltGrp gens ≤ S16C11SetStab (S16C11AltAct n)
        {S16C11AltCls n x₀, S16C11AltCls n xa, S16C11AltCls n xb} ∧
      (S16C11AltGrp gens).relIndex (S16C11SetStab (S16C11AltAct n)
        {S16C11AltCls n x₀, S16C11AltCls n xa, S16C11AltCls n xb}) = 3 ∧
      ∃ g ∈ S16C11SetStab (S16C11AltAct n)
        {S16C11AltCls n x₀, S16C11AltCls n xa, S16C11AltCls n xb},
        S16C11AltAct n g (S16C11AltCls n x₀) ≠ S16C11AltCls n x₀ := by
  set Y : Set (FFModel.altDn n).Mod :=
    {S16C11AltCls n x₀, S16C11AltCls n xa, S16C11AltCls n xb} with hY
  have hfixT : ∀ t ∈ S16C11AltGrp gens,
      S16C11AltAct n t (S16C11AltCls n x₀) = S16C11AltCls n x₀ :=
    s16c11_alt_grp_fixes fun g hg => (s16c11_alt_fixed_iff g h₀).mpr (hfix g hg)
  have hTS : S16C11AltGrp gens ≤ S16C11SetStab (S16C11AltAct n) Y := by
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    rw [hY]
    exact (s16c11_alt_mem_setStab_iff h₀ ha hb g).mpr (hstab g hg)
  have hstab_eq : S16C11SetStab (S16C11AltAct n) Y ⊓
      (MulAction.stabilizer (MulAut (FFModel.altDn n).Mod) (S16C11AltCls n x₀)).comap
        (S16C11AltAct n) = S16C11AltGrp gens := by
    refine le_antisymm ?_ ?_
    · intro g hg
      let g' : ↥(alternatingGroup (Fin n)) := g
      obtain ⟨hgS, hgstab⟩ := Subgroup.mem_inf.1 hg
      have hgTriple : S16C11AltTriple x₀ xa xb (g' : Equiv.Perm (Fin n)) := by
        rw [hY] at hgS
        exact (s16c11_alt_mem_setStab_iff h₀ ha hb g').mp hgS
      have hfixg : S16C11AltEqv x₀ (S16C11AltPact (g' : Equiv.Perm (Fin n)) x₀) :=
        (s16c11_alt_fixed_iff g' h₀).mp
          (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_comap.1 hgstab))
      have hsign : Equiv.Perm.sign (g' : Equiv.Perm (Fin n)) = 1 :=
        Equiv.Perm.mem_alternatingGroup.mp g'.2
      have hmem := hpass (g' : Equiv.Perm (Fin n)) hgTriple hfixg hsign
      have hgWords : g ∈ S16C11AltWords gens m := by
        obtain ⟨g', hg', hgg'⟩ := Finset.mem_image.1 hmem
        have hgg : g' = g := Subtype.ext hgg'
        rwa [hgg] at hg'
      exact s16c11_alt_words_subset_closure gens m hgWords
    · intro t ht
      exact Subgroup.mem_inf.2 ⟨hTS ht,
        Subgroup.mem_comap.2 (MulAction.mem_stabilizer_iff.2 (hfixT t ht))⟩
  have hOrb : {z : (FFModel.altDn n).Mod | ∃ x ∈ S16C11SetStab (S16C11AltAct n) Y,
      S16C11AltAct n x (S16C11AltCls n x₀) = z} = Y := by
    ext z
    constructor
    · rintro ⟨x, hxS, rfl⟩
      have hxstab : S16C11AltAct n x ∈
          MulAction.stabilizer (MulAut (FFModel.altDn n).Mod) Y := by
        rw [S16C11SetStab] at hxS
        exact Subgroup.mem_comap.1 hxS
      have hx₀Y : S16C11AltCls n x₀ ∈ Y := by
        rw [hY]
        simp
      exact (MulAction.mem_stabilizer_set.mp hxstab (S16C11AltCls n x₀)).mpr hx₀Y
    · intro hz
      rw [hY] at hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨1, (S16C11SetStab (S16C11AltAct n) Y).one_mem, by simp⟩
      · have hsaS : sa ∈ S16C11SetStab (S16C11AltAct n) Y := by
          rw [hY]
          exact (s16c11_alt_mem_setStab_iff h₀ ha hb sa).mpr hsa
        have hsum : ∑ i, S16C11AltPact (sa : Equiv.Perm (Fin n)) x₀ i = 0 := by
          rw [s16c11_alt_sum_pact]
          exact h₀
        refine ⟨sa, hsaS, ?_⟩
        exact (s16c11_alt_act_cls sa h₀).trans
          ((s16c11_alt_cls_eq_iff ha hsum).mpr hsa').symm
      · have hsbS : sb ∈ S16C11SetStab (S16C11AltAct n) Y := by
          rw [hY]
          exact (s16c11_alt_mem_setStab_iff h₀ ha hb sb).mpr hsb
        have hsum : ∑ i, S16C11AltPact (sb : Equiv.Perm (Fin n)) x₀ i = 0 := by
          rw [s16c11_alt_sum_pact]
          exact h₀
        refine ⟨sb, hsbS, ?_⟩
        exact (s16c11_alt_act_cls sb h₀).trans
          ((s16c11_alt_cls_eq_iff hb hsum).mpr hsb').symm
  have hYcard : Y.ncard = 3 := by
    refine Set.ncard_eq_three.mpr
      ⟨S16C11AltCls n x₀, S16C11AltCls n xa, S16C11AltCls n xb, ?_, ?_, ?_, hY⟩
    · intro h
      exact hxa ((s16c11_alt_cls_eq_iff h₀ ha).mp h)
    · intro h
      exact hxb ((s16c11_alt_cls_eq_iff h₀ hb).mp h)
    · intro h
      exact hab ((s16c11_alt_cls_eq_iff ha hb).mp h)
  refine ⟨hTS, ?_, ?_⟩
  · haveI : Finite (FFModel.altDn n).Gam :=
      inferInstanceAs (Finite ↥(alternatingGroup (Fin n)))
    have hrel := s16c11_altforced_ncard_orbit_eq_relIndex (ρ := S16C11AltAct n)
      (T := S16C11AltGrp gens) (X := S16C11SetStab (S16C11AltAct n) Y)
      (y := S16C11AltCls n x₀) hstab_eq
    calc (S16C11AltGrp gens).relIndex (S16C11SetStab (S16C11AltAct n) Y)
        = {z | ∃ x ∈ S16C11SetStab (S16C11AltAct n) Y,
            S16C11AltAct n x (S16C11AltCls n x₀) = z}.ncard := hrel.symm
      _ = Y.ncard := congrArg Set.ncard hOrb
      _ = 3 := hYcard
  · have hsaS : sa ∈ S16C11SetStab (S16C11AltAct n) Y := by
      rw [hY]
      exact (s16c11_alt_mem_setStab_iff h₀ ha hb sa).mpr hsa
    have hsum : ∑ i, S16C11AltPact (sa : Equiv.Perm (Fin n)) x₀ i = 0 := by
      rw [s16c11_alt_sum_pact]
      exact h₀
    have hact : S16C11AltAct n sa (S16C11AltCls n x₀) = S16C11AltCls n xa :=
      (s16c11_alt_act_cls sa h₀).trans ((s16c11_alt_cls_eq_iff ha hsum).mpr hsa').symm
    have hne : S16C11AltCls n xa ≠ S16C11AltCls n x₀ := fun h =>
      hxa ((s16c11_alt_cls_eq_iff h₀ ha).mp h.symm)
    refine ⟨sa, hsaS, ?_⟩
    intro h
    exact hne (hact ▸ h)

theorem s16c11_alt_forced_even_of_checks {n : ℕ} (gens : List ↥(alternatingGroup (Fin n)))
    (m e c : ℕ) (hfixw : S16C11AltWords gens (m + 1) = S16C11AltWords gens m)
    (hcard : (S16C11AltWords gens m).card = 2 ^ e)
    (hgroup : Nat.card ↥(alternatingGroup (Fin n)) = 2 ^ e * c) (hc : ¬ 2 ∣ c)
    {x₀ xa xb : Fin n → ZMod 2} (sa sb : ↥(alternatingGroup (Fin n))) (h₀ : ∑ i, x₀ i = 0)
    (ha : ∑ i, xa i = 0) (hb : ∑ i, xb i = 0) (hne : ¬ S16C11AltEqv 0 x₀)
    (hxa : ¬ S16C11AltEqv x₀ xa) (hxb : ¬ S16C11AltEqv x₀ xb) (hab : ¬ S16C11AltEqv xa xb)
    (hfix : ∀ g ∈ gens, S16C11AltEqv x₀ (S16C11AltPact (g : Equiv.Perm (Fin n)) x₀))
    (hstab : ∀ g ∈ gens, S16C11AltTriple x₀ xa xb (g : Equiv.Perm (Fin n)))
    (huniq : ∀ k : Fin (2 ^ n), ∑ i, S16C11AltBits n k i = 0 →
      ¬ S16C11AltEqv 0 (S16C11AltBits n k) →
      (∀ g ∈ gens, S16C11AltEqv (S16C11AltBits n k)
        (S16C11AltPact (g : Equiv.Perm (Fin n)) (S16C11AltBits n k))) →
      S16C11AltEqv x₀ (S16C11AltBits n k))
    (hpair : ∀ k : Fin (2 ^ n), S16C11AltWt (S16C11AltBits n k) = S16C11AltWt x₀ →
      ¬ S16C11AltEqv x₀ (S16C11AltBits n k) → ¬ S16C11AltEqv xa (S16C11AltBits n k) →
      ¬ S16C11AltEqv xb (S16C11AltBits n k) →
      ∃ t₁ ∈ S16C11AltWords gens m, ∃ t₂ ∈ S16C11AltWords gens m,
        ¬ S16C11AltEqv (S16C11AltBits n k)
          (S16C11AltPact (t₁ : Equiv.Perm (Fin n)) (S16C11AltBits n k)) ∧
        ¬ S16C11AltEqv (S16C11AltBits n k)
          (S16C11AltPact (t₂ : Equiv.Perm (Fin n)) (S16C11AltBits n k)) ∧
        ¬ S16C11AltEqv (S16C11AltPact (t₁ : Equiv.Perm (Fin n)) (S16C11AltBits n k))
          (S16C11AltPact (t₂ : Equiv.Perm (Fin n)) (S16C11AltBits n k)))
    (hpass : ∀ g : Equiv.Perm (Fin n), S16C11AltTriple x₀ xa xb g →
      S16C11AltEqv x₀ (S16C11AltPact g x₀) → Equiv.Perm.sign g = 1 →
      g ∈ (S16C11AltWords gens m).image Subtype.val)
    (hsa : S16C11AltTriple x₀ xa xb (sa : Equiv.Perm (Fin n)))
    (hsa' : S16C11AltEqv xa (S16C11AltPact (sa : Equiv.Perm (Fin n)) x₀))
    (hsb : S16C11AltTriple x₀ xa xb (sb : Equiv.Perm (Fin n)))
    (hsb' : S16C11AltEqv xb (S16C11AltPact (sb : Equiv.Perm (Fin n)) x₀)) :
    ∃ (T₁ : Subgroup (FFModel.altDn n).Gam) (N : ℕ) (y₀ a b : (FFModel.altDn n).Mod),
      IsPGroup 2 ↥T₁ ∧ ¬ 2 ∣ T₁.index ∧ S16C11Forced (S16C11AltAct n) T₁ N y₀ a b ∧
      T₁ ≤ S16C11SetStab (S16C11AltAct n) {y₀, a, b} ∧
      T₁.relIndex (S16C11SetStab (S16C11AltAct n) {y₀, a, b}) = 3 ∧
      ∃ g ∈ S16C11SetStab (S16C11AltAct n) {y₀, a, b}, S16C11AltAct n g y₀ ≠ y₀ := by
  obtain ⟨hP, hidx⟩ := s16c11_alt_pgroup_of_words gens m e c hfixw hcard hgroup hc
  have hws : ∀ t ∈ S16C11AltWords gens m, t ∈ S16C11AltGrp gens := fun t ht =>
    s16c11_alt_words_subset_closure gens m ht
  have horb : {z : (FFModel.altDn n).Mod | ∃ g : ↥(alternatingGroup (Fin n)),
      S16C11AltAct n g (S16C11AltCls n x₀) = z}.ncard ≤ Nat.card (FFModel.altDn n).Mod :=
    Set.ncard_le_card _
  have huniq' := s16c11_alt_uniq_of_check gens h₀ (Nat.card (FFModel.altDn n).Mod) huniq
  have hF := s16c11_alt_forced_of_checks gens (S16C11AltWords gens m) hws h₀ ha hb hne hfix horb
    huniq' hab hpair
  obtain ⟨hT, h3, hmov⟩ := s16c11_alt_stab_data_of_checks gens m hfixw sa sb h₀ ha hb hxa hxb hab
    hfix hstab hpass hsa hsa' hsb hsb'
  exact ⟨S16C11AltGrp gens, Nat.card (FFModel.altDn n).Mod, _, _, _, hP, hidx, hF, hT, h3, hmov⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
