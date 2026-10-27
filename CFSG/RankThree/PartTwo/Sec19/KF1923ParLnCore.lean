module

public import CFSG.RankThree.PartTwo.Sec19.KF1923ParLnBlock
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFLin
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5

public section

namespace CFSG.RankThree.PartTwo.Late.KFParLn

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_cut {m : ℕ} (P : Subgroup (S2 m)) (hB : upperTriangular m (ZMod 2) ≤ P)
    (hP : P ≠ ⊤) : ∃ i, 1 ≤ i ∧ i < m ∧ P ≤ stabilizer (flagSpace m (ZMod 2) i) := by
  obtain ⟨hPeq, -⟩ := borel_overgroups P hB
  by_cases hI : borelOvergroupCuts P = ∅
  · exact absurd (by rw [hPeq, hI, flagStabilizer_empty]) hP
  · obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.2 hI
    have ⟨hi1, him, _⟩ := hi
    refine ⟨i, hi1, him, fun g hg => ?_⟩
    have hg' : g ∈ flagStabilizer m (ZMod 2) (borelOvergroupCuts P) := by rwa [← hPeq]
    exact mem_flagStabilizer.1 hg' i hi

theorem eq_bot_or_eq_of_invariant {H : Type} [Group H] {E K : Subgroup H} {y : H}
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE9 : Nat.card E = 9)
    (hinv : ∀ e ∈ E, y ^ 2 * e * (y ^ 2)⁻¹ = e⁻¹)
    (hKE : K ≤ E) (hK : ∀ k ∈ K, y * k * y⁻¹ ∈ K) : K = ⊥ ∨ K = E := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hKbot, hKE'⟩ := hcon
  haveI : Finite E := Nat.finite_of_card_ne_zero (by omega)
  haveI : Finite K :=
    Finite.of_injective (Subgroup.inclusion hKE) (Subgroup.inclusion_injective hKE)
  have hdvd : Nat.card K ∣ 9 := hE9 ▸ Subgroup.card_dvd_of_le hKE
  have hcard3 : Nat.card K = 3 := by
    have h1 : Nat.card K ≠ 1 := fun h => hKbot (Subgroup.eq_bot_of_card_eq K h)
    have h9 : Nat.card K ≠ 9 := fun h => hKE' (Subgroup.eq_of_le_of_card_ge hKE (by omega))
    have hmem : Nat.card K ∈ Nat.divisors 9 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have hd : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hd] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  obtain ⟨⟨k, hk⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hKbot
  have hk1' : k ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hk3 : k ^ 3 = 1 := hE3 k (hKE hk)
  have hord : orderOf k = 3 := orderOf_eq_prime hk3 hk1'
  have hzp : Subgroup.zpowers k = K := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.zpowers_le]; exact hk
    · rw [Nat.card_zpowers, hord, hcard3]
  have hyk : y * k * y⁻¹ ∈ Subgroup.zpowers k := hzp ▸ hK k hk
  obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.1 hyk
  have hne : k ^ c ≠ 1 := by
    rw [hc]
    intro h
    apply hk1'
    have := congrArg (fun x => y⁻¹ * x * y) h
    simpa [mul_assoc] using this
  have hc3 : ¬ (3 : ℤ) ∣ c := by
    intro hdiv
    apply hne
    exact (orderOf_dvd_iff_zpow_eq_one (x := k) (i := c)).1 (by rw [hord]; exact_mod_cast hdiv)
  have hsq : (c * c) % 3 = 1 := by
    have : c % 3 = 1 ∨ c % 3 = 2 := by omega
    rcases this with h | h <;> simp [Int.mul_emod, h]
  have h2 : y ^ 2 * k * (y ^ 2)⁻¹ = k ^ (c * c) := by
    calc y ^ 2 * k * (y ^ 2)⁻¹ = y * (y * k * y⁻¹) * y⁻¹ := by rw [pow_two]; group
      _ = y * k ^ c * y⁻¹ := by rw [← hc]
      _ = (y * k * y⁻¹) ^ c := (conj_zpow).symm
      _ = k ^ (c * c) := by rw [← hc, ← _root_.zpow_mul]
  have h3 : k ^ (c * c) = k := by
    rw [← zpow_mod_orderOf, hord]
    have : ((3 : ℕ) : ℤ) = 3 := rfl
    rw [this, hsq, zpow_one]
  have h4 := hinv k (hKE hk)
  rw [h2, h3] at h4
  have h5 : k ^ 2 = 1 := by
    have : k * k = 1 := by
      calc k * k = k * k⁻¹ := by rw [← h4]
        _ = 1 := mul_inv_cancel k
    rwa [← pow_two] at this
  apply hk1'
  calc k = k ^ 3 * (k ^ 2)⁻¹ := by group
    _ = 1 := by rw [hk3, h5]; simp

structure Cfg {H : Type} [Group H] (R E : Subgroup H) (y : H) : Prop where
  normal : ∀ h r : H, r ∈ R → h * r * h⁻¹ ∈ R
  solvable : Group.IsSolvable ↥R
  le : E ≤ R
  exp3 : ∀ x ∈ E, x ^ 3 = 1
  card : Nat.card E = 9
  inv_mem : ∀ e ∈ E, y * e * y⁻¹ ∈ E
  inv : ∀ e ∈ E, y ^ 2 * e * (y ^ 2)⁻¹ = e⁻¹

variable {H : Type} [Group H] {R E : Subgroup H} {y : H}

theorem Cfg.ne_bot (hc : Cfg R E y) : E ≠ ⊥ := by
  intro h
  have := hc.card
  rw [h] at this
  simp at this

theorem Cfg.false_of_small (hc : Cfg R E y) {m : ℕ} (hm : 1 ≤ m) (hm2 : m ≤ 2)
    (ι : H →* S2 m) (hinj : ∀ e ∈ E, ι e = 1 → e = 1) : False := by
  have hinj' : Function.Injective (ι.comp E.subtype) := by
    intro a b hab
    apply Subtype.ext
    have h1 : ι (a.1 * b.1⁻¹) = 1 := by
      have : ι a.1 = ι b.1 := hab
      rw [map_mul, map_inv, this, mul_inv_cancel]
    have h2 := hinj _ (E.mul_mem a.2 (E.inv_mem b.2)) h1
    exact mul_inv_eq_one.1 h2
  have hdvd := Subgroup.card_dvd_of_injective _ hinj'
  rw [hc.card] at hdvd
  have hcard : Nat.card (S2 m) = 1 ∨ Nat.card (S2 m) = 6 := by
    interval_cases m
    · left
      rw [CFSG.RankThree.PartTwo.Sec4.RonanK429F.card_SL_zmod_two (by norm_num)]
      decide
    · right
      rw [CFSG.RankThree.PartTwo.Sec4.RonanK429F.card_SL_zmod_two (by norm_num)]
      decide
  rcases hcard with h | h <;> rw [h] at hdvd <;> omega

theorem Cfg.false_of_surjective (hc : Cfg R E y) {m : ℕ} (hm : 3 ≤ m) (ι : H →* S2 m)
    (hinj : ∀ e ∈ E, ι e = 1 → e = 1) (hsurj : Function.Surjective ι) : False := by
  haveI hS : IsSimpleGroup (S2 m) :=
    CFSG.RankThree.PartTwo.Sec4.RonanK429F.isSimpleGroup_SL_zmod_two hm
  haveI hN : (R.map ι).Normal := ⟨fun n hn s => by
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hn
    obtain ⟨h, rfl⟩ := hsurj s
    exact Subgroup.mem_map.2 ⟨h * r * h⁻¹, hc.normal h r hr, by simp⟩⟩
  haveI := hc.solvable
  haveI hsolv : Group.IsSolvable ↥(R.map ι) :=
    Group.isSolvable_of_surjective (f := ι.subgroupMap R) (MonoidHom.subgroupMap_surjective ι R)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.map ι) with h | h
  · apply hc.ne_bot
    rw [eq_bot_iff]
    intro e he
    have : ι e ∈ R.map ι := Subgroup.mem_map_of_mem ι (hc.le he)
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (hinj e he this)
  · rw [h] at hsolv
    let eT : ↥(⊤ : Subgroup (S2 m)) ≃* S2 m := Subgroup.topEquiv
    haveI : Group.IsSolvable (S2 m) :=
      Group.isSolvable_of_surjective (f := eT.toMonoidHom) eT.surjective
    obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.sl_nonabelian_of_card_two
      (K := ZMod 2) (Nat.card_zmod 2) hm
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 this a b)

theorem Cfg.ker_eq {G' : Type*} [Group G'] (hc : Cfg R E y) (f : H →* G') :
    f.ker ⊓ E = ⊥ ∨ f.ker ⊓ E = E :=
  eq_bot_or_eq_of_invariant hc.exp3 hc.card hc.inv inf_le_right (fun k hk => ⟨by
    have h1 : f (y * k * y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.1 hk.1]
      simp
    exact MonoidHom.mem_ker.2 h1, hc.inv_mem k hk.2⟩)

theorem Cfg.inj_of_ker_eq_bot {G' : Type*} [Group G'] {f : H →* G'} (hbot : f.ker ⊓ E = ⊥) :
    ∀ e ∈ E, f e = 1 → e = 1 := fun e he hfe => by
  have : e ∈ f.ker ⊓ E := ⟨MonoidHom.mem_ker.2 hfe, he⟩
  rw [hbot] at this
  exact Subgroup.mem_bot.1 this

theorem Cfg.false_of_hom (hc : Cfg R E y) :
    ∀ m : ℕ, 1 ≤ m → ∀ ι : H →* S2 m, (∀ e ∈ E, ι e = 1 → e = 1) →
      upperTriangular m (ZMod 2) ≤ ι.range → False := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm ι hinj hB
  by_cases hsmall : m ≤ 2
  · exact hc.false_of_small hm hsmall ι hinj
  have hm3 : 3 ≤ m := by omega
  by_cases htop : ι.range = ⊤
  · exact hc.false_of_surjective hm3 ι hinj (MonoidHom.range_eq_top.1 htop)
  obtain ⟨i, hi1, him, hP⟩ := exists_cut ι.range hB htop
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le him.le
  have hj : 1 ≤ j := by omega
  have hstab : ∀ h : H, ι h ∈ stabilizer (flagSpace (i + j) (ZMod 2) i) :=
    fun h => hP ⟨h, rfl⟩
  let ι' : H →* ↥(stabilizer (flagSpace (i + j) (ZMod 2) i)) := ι.codRestrict _ hstab
  let ι₁ : H →* S2 i := (blockHom1 i j).comp ι'
  let ι₂ : H →* S2 j := (blockHom2 i j).comp ι'
  rcases hc.ker_eq ι₁ with h1 | h1
  · refine ih i (by omega) hi1 ι₁ (Cfg.inj_of_ker_eq_bot h1) ?_
    intro b hb
    obtain ⟨g, hg, hgb⟩ := exists_block1_upper hb j
    obtain ⟨h, hh⟩ := hB hg
    refine ⟨h, ?_⟩
    have : ι' h = g := Subtype.ext hh
    show blockHom1 i j (ι' h) = b
    rw [this, hgb]
  rcases hc.ker_eq ι₂ with h2 | h2
  · refine ih j (by omega) hj ι₂ (Cfg.inj_of_ker_eq_bot h2) ?_
    intro b hb
    obtain ⟨g, hg, hgb⟩ := exists_block2_upper hb i
    obtain ⟨h, hh⟩ := hB hg
    refine ⟨h, ?_⟩
    have : ι' h = g := Subtype.ext hh
    show blockHom2 i j (ι' h) = b
    rw [this, hgb]
  · apply hc.ne_bot
    rw [eq_bot_iff]
    intro e he
    have h1e : ι₁ e = 1 := MonoidHom.mem_ker.1 (by rw [← h1] at he; exact he.1)
    have h2e : ι₂ e = 1 := MonoidHom.mem_ker.1 (by rw [← h2] at he; exact he.1)
    have hsq : (ι' e : S2 (i + j)) * ι' e = 1 := sq_eq_one_of_blocks (ι' e) h1e h2e
    have hsq' : ι (e * e) = 1 := by
      rw [map_mul]
      exact hsq
    have he2 : e * e = 1 := hinj _ (E.mul_mem he he) hsq'
    have he3 : e ^ 3 = 1 := hc.exp3 e he
    refine Subgroup.mem_bot.2 ?_
    calc e = e ^ 3 * (e * e)⁻¹ := by group
      _ = 1 := by rw [he3, he2]; simp

end CFSG.RankThree.PartTwo.Late.KFParLn
