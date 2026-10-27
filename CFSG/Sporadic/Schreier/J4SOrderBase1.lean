
module

public import CFSG.Sporadic.Schreier.J4SOrderBase

public import CFSG.Sporadic.Schreier.J4SOrbitCheck
public import CFSG.Sporadic.Schreier.J4SChain
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.SectionRank CFSG.SectionRank.Native
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem ksetCheck_parts :
    O.vmul ksetVectors[0]! Zn.1 < 2 ^ 112 ∧ ∀ i < ksetSize, ksetVectors[i]! < 2 ^ 112 ∧
      (ksetEdges[i]!)[0]! < ksetSize ∧
      ksetVectors[(ksetEdges[i]!)[0]!]! = O.vmul ksetVectors[i]! Xn.1 ∧
      (ksetEdges[i]!)[1]! < ksetSize ∧
      ksetVectors[(ksetEdges[i]!)[1]!]! = O.vmul ksetVectors[i]! Yn.1 ∧
      ksetVectors[i]! ≠ O.vmul ksetVectors[0]! Zn.1 :=
  ⟨kset_w_lt, kset_all⟩

theorem kset_invariant :
    ∀ g ∈ K, ∀ w ∈ ksetRows, g • w ∈ ksetRows := by
  refine smul_mem_of_inv_gens ?_
  rintro g (rfl | rfl) w ⟨i, hi, rfl⟩
  · obtain ⟨-, h2, h3, -⟩ := ksetCheck_parts.2 i hi
    refine ⟨_, h2, ?_⟩
    rw [kvec, kvec, inv_smul_toRow (rep_x matFacts), h3]
  · obtain ⟨-, -, -, h4, h5, -⟩ := ksetCheck_parts.2 i hi
    refine ⟨_, h4, ?_⟩
    rw [kvec, kvec, inv_smul_toRow (rep_y matFacts), h5]

theorem z_not_mem_K : z ∉ K := by
  intro hz
  have h := kset_invariant z⁻¹ (K.inv_mem hz) (kvec 0) ⟨0, by norm_num [ksetSize], rfl⟩
  rw [kvec, inv_smul_toRow (rep_z matFacts)] at h
  obtain ⟨j, hj, e⟩ := h
  have hj' : j < ksetSize := hj
  obtain ⟨h1, -, -, -, -, h7⟩ := ksetCheck_parts.2 j hj'
  exact h7 (toVecD_injective h1 ksetCheck_parts.1 e)

theorem η_one_ne_one : η 1 ≠ 1 := by
  intro h
  have := η_injOn (i := 1) (k := 0) (by norm_num) (by norm_num) (h.trans η_zero.symm)
  omega

theorem reach1
    (i : ℕ) (hi : i < 1771) : ∃ k ∈ K, k * η 1 * k⁻¹ = η orb1.1[i]! :=
  reach_of_bfsOK orb1_ok K xy_gens i hi

theorem reach14
    (i : ℕ) (hi : i < 276) : ∃ k ∈ K, k * η 14 * k⁻¹ = η orb14.1[i]! :=
  reach_of_bfsOK orb14_ok K xy_gens i hi

theorem cover (a : ℕ) (ha : a < 2048) :
    a = 0 ∨ (∃ i < 1771, orb1.1[i]! = a) ∨ ∃ i < 276, orb14.1[i]! = a := by
  have h := coverCheck_eq
  unfold coverCheck at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    at h
  rcases h a ha with (h0 | ⟨i, hi, e⟩) | ⟨i, hi, e⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl ⟨i, hi, e⟩)
  · exact Or.inr (Or.inr ⟨i, hi, e⟩)

theorem conj_mem_K_inf_N
    {k d : J} (hk : k ∈ K) (hd : d ∈ K ⊓ N) : k * d * k⁻¹ ∈ K ⊓ N :=
  ⟨K.mul_mem (K.mul_mem hk hd.1) (K.inv_mem hk), conj_mem_N_of_mem_K hk hd.2⟩

theorem conj_inv_mem_K_inf_N
    {k d : J} (hk : k ∈ K) (hd : k * d * k⁻¹ ∈ K ⊓ N) : d ∈ K ⊓ N := by
  have := conj_mem_K_inf_N (K.inv_mem hk) hd
  rwa [show k⁻¹ * (k * d * k⁻¹) * k⁻¹⁻¹ = d by group] at this

theorem card_ge_of_pts
    {D : Subgroup J} {pts : Array ℕ} {m : ℕ} (hlt : ∀ i < m, pts[i]! < 2048)
    (hne : ∀ i < m, ∀ k < m, i ≠ k → pts[i]! ≠ pts[k]!) (hnz : ∀ i < m, pts[i]! ≠ 0)
    (hmem : ∀ i < m, η pts[i]! ∈ D) : m + 1 ≤ Nat.card D := by
  have hwlt : ∀ i : Fin (m + 1), withZero pts i < 2 ^ 11 := by
    intro i
    unfold withZero
    split_ifs with h
    · norm_num
    · exact hlt _ (by omega)
  have hinj : Function.Injective fun i : Fin (m + 1) => withZero pts i := by
    intro i k e
    simp only [withZero] at e
    apply Fin.ext
    split_ifs at e with h1 h2 h2
    · omega
    · exact absurd e.symm (hnz _ (by omega))
    · exact absurd e (hnz _ (by omega))
    · by_contra hik
      exact hne _ (by omega) _ (by omega) (by omega) e
  have hD : ∀ i : Fin (m + 1), η (withZero pts i) ∈ D := by
    intro i
    unfold withZero
    split_ifs with h
    · rw [η_zero]; exact D.one_mem
    · exact hmem _ (by omega)
  have := Nat.card_le_card_of_injective (fun i : Fin (m + 1) => (⟨η (withZero pts i), hD i⟩ : D))
    fun i k e => by
      have h := Subtype.ext_iff.1 e
      dsimp only at h
      exact hinj (η_injOn (hwlt i) (hwlt k) h)
  simpa using this

theorem card_le_of_pts {D : Subgroup J} {pts : Array ℕ} {m : ℕ}
    (hD : ∀ d ∈ D, d = 1 ∨ ∃ i < m, d = η pts[i]!) : Nat.card D ≤ m + 1 := by
  have hsub : (D : Set J) ⊆ Set.range fun i : Fin (m + 1) => η (withZero pts i) := by
    intro d hd
    rcases hD d hd with rfl | ⟨i, hi, rfl⟩
    · exact ⟨0, by simp [withZero, η_zero]⟩
    · exact ⟨⟨i + 1, by omega⟩, by simp [withZero]⟩
  have h1 := Set.ncard_le_ncard hsub (Set.finite_range _)
  have h2 : Nat.card D = (D : Set J).ncard := Nat.card_coe_set_eq (D : Set J)
  have h3 := Finite.card_range_le fun i : Fin (m + 1) => η (withZero pts i)
  rw [← Nat.card_coe_set_eq, Nat.card_fin] at *
  rw [h2]
  exact h1.trans h3

theorem pts_ne_zero_of_reach {pts : Array ℕ} {m s : ℕ} (hs : η s ≠ 1)
    (hreach : ∀ i < m, ∃ k ∈ K, k * η s * k⁻¹ = η pts[i]!) (i : ℕ) (hi : i < m) :
    pts[i]! ≠ 0 := by
  intro h0
  obtain ⟨k, -, e⟩ := hreach i hi
  rw [h0, η_zero] at e
  apply hs
  calc η s = k⁻¹ * (k * η s * k⁻¹) * k := by group
    _ = 1 := by rw [e]; group

theorem eq_bot_or_eq_N
    {D : Subgroup J} (hDN : D ≤ N)
    (hK : ∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ ∈ D) : D = ⊥ ∨ D = N := by
  have hdvd : Nat.card D ∣ 2 ^ 11 := card_N ▸ Subgroup.card_dvd_of_le hDN
  have hinv : ∀ k ∈ K, ∀ d : J, k * d * k⁻¹ ∈ D → d ∈ D := by
    intro k hk d hd
    have := hK _ (K.inv_mem hk) _ hd
    rwa [show k⁻¹ * (k * d * k⁻¹) * k⁻¹⁻¹ = d by group] at this
  have hnz1 := pts_ne_zero_of_reach η_one_ne_one reach1
  by_cases h1 : η 1 ∈ D
  ·
    right
    have hc := card_ge_of_pts (D := D) (m := 1771) (fun i hi => bfsOK_lt orb1_ok hi)
      (fun i hi k hk hik => bfsOK_ne orb1_ok hi hk hik) hnz1 (fun i hi => by
        obtain ⟨k, hk, e⟩ := reach1 i hi
        rw [← e]
        exact hK k hk _ h1)
    have hpow : Nat.card D = 2 ^ 11 := by
      obtain ⟨e, hle, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      rw [he] at hc ⊢
      interval_cases e
      all_goals first | rfl | (exfalso; norm_num at hc)
    exact Subgroup.eq_of_le_of_card_ge hDN (by rw [hpow, card_N])
  ·
    left
    have hsub : ∀ d ∈ D, d = 1 ∨ ∃ i < 276, d = η orb14.1[i]! := by
      intro d hd
      obtain ⟨a, ha, rfl⟩ := exists_η_eq (hDN hd)
      rcases cover a ha with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · exact Or.inl η_zero
      · exfalso
        obtain ⟨k, hk, e⟩ := reach1 i hi
        have hd' : k * η 1 * k⁻¹ ∈ D := by rw [e]; exact hd
        exact h1 (hinv k hk _ hd')
      · exact Or.inr ⟨i, hi, rfl⟩
    rw [eq_bot_iff]
    intro d hd
    rw [Subgroup.mem_bot]
    by_contra hd1
    obtain ⟨i, hi, rfl⟩ := (hsub d hd).resolve_left hd1
    have h14 : η 14 ∈ D := by
      obtain ⟨k, hk, e⟩ := reach14 i hi
      have hd' : k * η 14 * k⁻¹ ∈ D := by rw [e]; exact hd
      exact hinv k hk _ hd'
    have hnz14 := pts_ne_zero_of_reach (s := 14) (fun h => by
      have := η_injOn (i := 14) (k := 0) (by norm_num) (by norm_num) (h.trans η_zero.symm)
      omega) reach14
    have hc := card_ge_of_pts (D := D) (m := 276) (fun i hi => bfsOK_lt orb14_ok hi)
      (fun i hi k hk hik => bfsOK_ne orb14_ok hi hk hik) hnz14 (fun i hi => by
        obtain ⟨k, hk, e⟩ := reach14 i hi
        rw [← e]
        exact hK k hk _ h14)
    have h277 : Nat.card D = 277 := le_antisymm (card_le_of_pts hsub) hc
    rw [h277] at hdvd
    norm_num at hdvd

theorem K_inf_N : K ⊓ N = ⊥ := by
  refine (eq_bot_or_eq_N inf_le_right fun k hk d hd => conj_mem_K_inf_N hk hd).resolve_right ?_
  intro hN
  exact z_not_mem_K ((hN.symm ▸ z_mem_N : z ∈ K ⊓ N).1)

@[expose] def ρK :
    K →* MulAut N := ρN.comp (Subgroup.inclusion K_le_normalizer)

@[expose] def ρH :
    H →* MulAut N := ρN.comp (Subgroup.inclusion H_le_normalizer)

theorem ρK_apply (k : K) (n : N) : ((ρK k n : N) : J) = k * n * (k : J)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

theorem ρH_apply (h : H) (n : N) : ((ρH h n : N) : J) = h * n * (h : J)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

theorem ρK_ηN
    {k : K} {a b : ℕ} (h : (k : J) * η a * (k : J)⁻¹ = η b) : ρK k (ηN a) = ηN b :=
  Subtype.ext (by rw [ρK_apply]; exact h)

abbrev P : Subgroup (MulAut N) := ρK.range

theorem ηN_injOn
    {a b : ℕ} (ha : a < 2 ^ 11) (hb : b < 2 ^ 11) (h : ηN a = ηN b) : a = b := by
  have h' := Subtype.ext_iff.1 h
  dsimp only [ηN] at h'
  exact η_injOn ha hb h'

theorem le_orbit_ncard
    {G : Subgroup (MulAut N)} {b : N} {pts : Array ℕ} {m : ℕ}
    (hlt : ∀ i < m, pts[i]! < 2048) (hne : ∀ i < m, ∀ k < m, i ≠ k → pts[i]! ≠ pts[k]!)
    (hmem : ∀ i < m, ηN pts[i]! ∈ MulAction.orbit G b) :
    m ≤ (MulAction.orbit G b).ncard := by
  have hf : Function.Injective fun i : Fin m => ηN pts[i.val]! := by
    intro i k e
    by_contra hik
    exact hne _ i.isLt _ k.isLt (fun h => hik (Fin.ext h))
      (ηN_injOn (hlt _ i.isLt) (hlt _ k.isLt) e)
  have hsub : Set.range (fun i : Fin m => ηN pts[i.val]!) ⊆ MulAction.orbit G b := by
    rintro _ ⟨i, rfl⟩
    exact hmem _ i.isLt
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_range_of_injective hf, Nat.card_fin] at h1
  exact h1

@[expose] def G1 : Subgroup (MulAut N) :=
  Subgroup.closure (Set.range fun g : Fin 8 => ρK (sgenK idx1[g.val]!))

@[expose] def G2 : Subgroup (MulAut N) :=
  Subgroup.closure (Set.range fun g : Fin 5 => ρK (sgenK idx2[g.val]!))

theorem fixCheck_parts :
    (∀ g < 8, app11 gens1[g]! 1 = 1) ∧ ∀ g < 5, app11 gens2[g]! 1 = 1 ∧ app11 gens2[g]! 2 = 2 := by
  have h := fixCheck_eq
  unfold fixCheck at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · exact beq_iff_eq.1 (h.1 g (List.mem_range.2 hg))
  · have := h.2 g (List.mem_range.2 hg)
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at this
    exact this

theorem sgenK_conj (m a : ℕ) :
    ((sgenK m : K) : J) * η a * ((sgenK m : K) : J)⁻¹ = η (app11 (sCols m) a) :=
  sgen_conj m a

theorem G1_le_P : G1 ≤ P := by
  rw [G1, Subgroup.closure_le]
  rintro _ ⟨g, rfl⟩
  exact ⟨_, rfl⟩

theorem G2_le_G1 : G2 ≤ G1 := by
  rw [G2, Subgroup.closure_le]
  rintro _ ⟨g, rfl⟩
  have hg := g.isLt
  have e : ∃ g' : Fin 8, idx1[g'.val]! = idx2[g.val]! := by
    obtain ⟨g, hg'⟩ := g
    interval_cases g
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
  obtain ⟨g', e⟩ := e
  beta_reduce
  rw [SetLike.mem_coe, ← e]
  exact Subgroup.subset_closure ⟨g', rfl⟩

theorem G1_fix :
    ∀ g ∈ G1, g • ηN 1 = ηN 1 := by
  have hle : G1 ≤ MulAction.stabilizer (MulAut N) (ηN 1) := by
    rw [G1, Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
    refine ρK_ηN ?_
    rw [sgenK_conj, ← gens1_eq _ g.isLt, fixCheck_parts.1 _ g.isLt]
  exact fun g hg => MulAction.mem_stabilizer_iff.1 (hle hg)

theorem G2_fix :
    ∀ g ∈ G2, g • ηN 2 = ηN 2 := by
  have hle : G2 ≤ MulAction.stabilizer (MulAut N) (ηN 2) := by
    rw [G2, Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
    refine ρK_ηN ?_
    rw [sgenK_conj, ← gens2_eq _ g.isLt, (fixCheck_parts.2 _ g.isLt).2]
  exact fun g hg => MulAction.mem_stabilizer_iff.1 (hle hg)

theorem mem_orbit_of_reach
    {G : Subgroup (MulAut N)} {s b : ℕ} {k : J}
    (hk : k ∈ (G.comap ρK).map K.subtype) (e : k * η s * k⁻¹ = η b) :
    ηN b ∈ MulAction.orbit G (ηN s) := by
  obtain ⟨k', hk', rfl⟩ := hk
  rw [Subgroup.coe_subtype] at e
  refine MulAction.mem_orbit_iff.2 ⟨⟨ρK k', Subgroup.mem_comap.1 hk'⟩, ?_⟩
  rw [Subgroup.mk_smul, MulAut.smul_def]
  exact ρK_ηN e

theorem gens1_reach :
    ∀ g < gens1.size, ∃ k ∈ (G1.comap ρK).map K.subtype,
    ∀ a, k * η a * k⁻¹ = η (app11 gens1[g]! a) := by
  intro g hg
  have hg8 : g < 8 := hg
  refine ⟨sgen idx1[g]!, ⟨sgenK idx1[g]!, Subgroup.subset_closure ⟨⟨g, hg8⟩, rfl⟩, rfl⟩,
    fun a => ?_⟩
  rw [gens1_eq g hg8]
  exact sgen_conj _ a

theorem gens2_reach :
    ∀ g < gens2.size, ∃ k ∈ (G2.comap ρK).map K.subtype,
    ∀ a, k * η a * k⁻¹ = η (app11 gens2[g]! a) := by
  intro g hg
  have hg5 : g < 5 := hg
  refine ⟨sgen idx2[g]!, ⟨sgenK idx2[g]!, Subgroup.subset_closure ⟨⟨g, hg5⟩, rfl⟩, rfl⟩,
    fun a => ?_⟩
  rw [gens2_eq g hg5]
  exact sgen_conj _ a

theorem xy_reach :
    ∀ g < xyGens.size, ∃ k ∈ (P.comap ρK).map K.subtype,
    ∀ a, k * η a * k⁻¹ = η (app11 xyGens[g]! a) := by
  intro g hg
  obtain ⟨k, hk, e⟩ := xy_gens g hg
  exact ⟨k, ⟨⟨k, hk⟩, ⟨_, rfl⟩, rfl⟩, e⟩

theorem card_P_ge :
    244823040 ≤ Nat.card P := by
  have o0 : 1771 ≤ (MulAction.orbit P (ηN 1)).ncard :=
    le_orbit_ncard (fun i hi => bfsOK_lt orb1_ok hi)
      (fun i hi k hk hik => bfsOK_ne orb1_ok hi hk hik) fun i hi => by
        obtain ⟨k, hk, e⟩ := reach_of_bfsOK orb1_ok _ xy_reach i hi
        exact mem_orbit_of_reach hk e
  have o1 : 1440 ≤ (MulAction.orbit G1 (ηN 2)).ncard :=
    le_orbit_ncard (fun i hi => bfsOK_lt orbB_ok hi)
      (fun i hi k hk hik => bfsOK_ne orbB_ok hi hk hik) fun i hi => by
        obtain ⟨k, hk, e⟩ := reach_of_bfsOK orbB_ok _ gens1_reach i hi
        exact mem_orbit_of_reach hk e
  have o2 : 96 ≤ (MulAction.orbit G2 (ηN 4)).ncard :=
    le_orbit_ncard (fun i hi => bfsOK_lt orbC_ok hi)
      (fun i hi k hk hik => bfsOK_ne orbC_ok hi hk hik) fun i hi => by
        obtain ⟨k, hk, e⟩ := reach_of_bfsOK orbC_ok _ gens2_reach i hi
        exact mem_orbit_of_reach hk e
  have hc := card_ge_of_orbit_chain G1_le_P G2_le_G1 (ηN 4) G1_fix G2_fix
  calc 244823040 = 1771 * 1440 * 96 := by norm_num
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul o0 o1) o2
    _ ≤ Nat.card P := hc

theorem rootCheck_parts :
    O.vmul rootBits Xn.1 = rootBits ∧ O.vmul rootBits Yn.1 = rootBits ∧
      O.vmul rootBits Zn.1 = rootBits := by
  have h := rootCheck_eq
  unfold rootCheck at h
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem H_le_stabilizer_v : H ≤ MulAction.stabilizer J v := by
  rw [H, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact smul_v_of (rep_x matFacts) rootCheck_parts.1
  · exact smul_v_of (rep_y matFacts) rootCheck_parts.2.1
  · exact smul_v_of (rep_z matFacts) rootCheck_parts.2.2

theorem ρK_eq (k : K) : ρK k = ρH (Subgroup.inclusion K_le_H k) := by
  ext n
  rw [ρK_apply, ρH_apply]
  rfl

theorem P_le_range_ρH : P ≤ ρH.range := by
  rintro _ ⟨k, rfl⟩
  exact ⟨_, (ρK_eq k).symm⟩

theorem N_le_ker_ρH : N.subgroupOf H ≤ ρH.ker := by
  intro h hh
  rw [Subgroup.mem_subgroupOf] at hh
  rw [MonoidHom.mem_ker]
  ext n
  rw [ρH_apply, MulAut.one_apply]
  have : IsMulCommutative N := N_isElementaryAbelian.toIsMulCommutative
  have hc : (h : J) * n = n * h := setLike_mul_comm hh n.2
  rw [hc, mul_inv_cancel_right]

end CFSG.Sporadic.J4Schreier
