module

public import CFSG.Sporadic.Recognition.JankoWongPGL

public section

open CFSG.GorensteinWalter (PGammaL2 PSL2 PGL2 IsOddPrimePower HasDihedralSylowTwo
  pGammaL2PSLRange pGammaL2PGLRange)

namespace CFSG.Sporadic.Recognition.JankoWong

namespace PSLStep

section Arithmetic

theorem eight_dvd_sq_sub_one {q : ℕ} (hq : Odd q) : 2 ^ 3 ∣ q ^ 2 - 1 := by
  obtain ⟨k, rfl⟩ := hq
  have h : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    apply Nat.sub_eq_of_eq_add
    ring
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  rw [h, hj]
  exact ⟨j, by ring⟩

end Arithmetic

section General

variable {K : Type*} [Group K]

theorem false_of_mulEquiv_alternatingGroup_seven_of_not_dvd (e : K ≃* alternatingGroup (Fin 7))
    (h : ¬ 2 ^ 3 ∣ Nat.card K) : False := by
  apply h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

end General

section Core

variable {K : Type} [Group K] {F : Type} [Field F] [Finite F]

theorem core_of_embedding (hF : IsOddPrimePower (Nat.card F)) {ι : K →* PGammaL2 F}
    (hι : Function.Injective ι) {M : Subgroup (PGammaL2 F)}
    (hM : M = pGammaL2PSLRange F ∨ M = pGammaL2PGLRange F) (hMle : M ≤ ι.range)
    (hodd : Odd (M.relIndex ι.range)) (h8 : ¬ 2 ^ 3 ∣ Nat.card K)
    {u : K} (hu : u ^ 2 = 1) (hu1 : u ≠ 1) {c : ℕ}
    (hcu : Nat.card (Subgroup.centralizer ({u} : Set K)) = c) (hc : c = 4 ∨ c = 12) :
    (Nat.card K = 12 ∧ c = 4) ∨ (Nat.card K = 60 ∧ IsSimpleGroup K ∧ c = 4) ∨
      (Nat.card K = 660 ∧ c = 12) ∨ (Nat.card K = 1092 ∧ c = 12) := by
  classical
  have hqodd : Odd (Nat.card F) := by
    obtain ⟨p, f, -, hpodd, -, hq⟩ := hF
    rw [hq]
    exact hpodd.pow
  have hMn : M.Normal := by
    rcases hM with rfl | rfl
    · exact CFSG.ABGDGroups.pGammaL2PSLRange_normal hF
    · infer_instance
  set L := M.comap ι with hL
  have hLn : L.Normal := hMn.comap ι
  have hLidx : L.index = M.relIndex ι.range := Subgroup.index_comap M ι
  have hLodd : Odd L.index := hLidx ▸ hodd
  have hLmap : L.map ι = M := Subgroup.map_comap_eq_self hMle
  have hLcard : Nat.card L = Nat.card M := by
    rw [← Subgroup.card_map_of_injective hι (K := L), hLmap]
  have hKcard : L.index * Nat.card L = Nat.card K := Subgroup.index_mul_card L
  have hMpsl : M = pGammaL2PSLRange F := by
    rcases hM with h | hMpgl
    · exact h
    · exfalso
      have hMcard : Nat.card M = Nat.card F * (Nat.card F ^ 2 - 1) := by
        rw [hMpgl, ← Nat.card_congr (CFSG.GorensteinWalter.pGammaL2PGLRangeEquiv F).toEquiv]
        exact CFSG.GorensteinWalter.pgl2_card_formula F
      apply h8
      rw [← hKcard, hLcard, hMcard]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (eight_dvd_sq_sub_one hqodd) _) _
  have hMcard : 2 * Nat.card M = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [hMpsl, ← Nat.card_congr (CFSG.GorensteinWalter.pGammaL2PSLRangeEquiv F).toEquiv,
      CFSG.GorensteinWalter.psl2_card_formula F hF]
    exact Nat.mul_div_cancel' (Dvd.dvd.mul_left (dvd_trans (by norm_num)
      (eight_dvd_sq_sub_one hqodd)) _)
  have hq8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5 := by
    apply PGLStep.mod_eight_of_two_part hqodd
    intro h
    apply h8
    rw [← hKcard, hLcard]
    rw [← hMcard] at h
    have h' : 2 ^ 3 ∣ Nat.card M :=
      Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) (by simpa [pow_succ, mul_comm] using h)
    exact Dvd.dvd.mul_left h' _
  obtain ⟨κ, hκι⟩ : ∃ κ : PSL2 F →* K, ∀ x,
      ι (κ x) = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL x) := by
    have h : ∀ x : PSL2 F, ∃ k : K,
        ι k = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL x) := fun x =>
      hMle (by rw [hMpsl]; exact ⟨x, rfl⟩)
    choose f hf using h
    exact ⟨MonoidHom.mk' f fun a b => hι (by rw [map_mul, hf, hf, hf, map_mul, map_mul]), hf⟩
  have hκinj : Function.Injective κ := fun a b hab =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      (SemidirectProduct.inl_injective (by rw [← hκι, ← hκι, hab]))
  have hmemL : ∀ y ∈ L, ∃ x, κ x = y := fun y hy => by
    have hy' : ι y ∈ M := hy
    rw [hMpsl] at hy'
    obtain ⟨x, hx⟩ := (CFSG.GorensteinWalter.mem_pGammaL2PSLRange_iff F _).mp hy'
    exact ⟨x, hι (by rw [hκι, hx])⟩
  have hκL : ∀ x, κ x ∈ L := fun x => by
    change ι (κ x) ∈ M
    rw [hκι, hMpsl]
    exact (CFSG.GorensteinWalter.mem_pGammaL2PSLRange_iff F _).mpr ⟨x, rfl⟩
  have hrange : κ.range = L := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact hκL x
    · intro hy
      obtain ⟨x, rfl⟩ := hmemL y hy
      exact ⟨x, rfl⟩
  have huL : u ∈ L := CFSG.ABGDGroups.mem_of_pow_two_pow_mem (N := L) hLodd (j := 1)
    (by rw [pow_one, hu]; exact L.one_mem)
  obtain ⟨t, rfl⟩ := hmemL u huL
  have ht2 : t ^ 2 = 1 := hκinj (by rw [map_pow, hu, map_one])
  have ht1 : t ≠ 1 := fun h => hu1 (by rw [h, map_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  obtain ⟨ε, hε, hε1⟩ : ∃ ε : ℤ, (Nat.card F : ℤ) ≡ ε [ZMOD 4] ∧ (ε = 1 ∨ ε = -1) := by
    obtain ⟨k, hk⟩ := hqodd
    by_cases h : Nat.card F % 4 = 1
    · exact ⟨1, by unfold Int.ModEq; omega, Or.inl rfl⟩
    · exact ⟨-1, by unfold Int.ModEq; omega, Or.inr rfl⟩
  obtain ⟨m, hm, ⟨eC⟩⟩ := CFSG.ABGDGroups.psl2_centralizer_involution_dihedral hF hε hε1 htord
  have hC0 : Nat.card (Subgroup.centralizer ({t} : Set (PSL2 F))) = 2 * m := by
    rw [Nat.card_congr eC.toEquiv, DihedralGroup.nat_card]
  have hcent : κ.range ⊓ Subgroup.centralizer ({κ t} : Set K) =
      (⊤ ⊓ Subgroup.centralizer ({t} : Set (PSL2 F))).map κ := by
    rw [CFSG.ABGDGroups.map_inf_centralizer_of_injective κ hκinj ⊤ t,
      ← MonoidHom.range_eq_map]
  have hcardC : Nat.card (κ.range ⊓ Subgroup.centralizer ({κ t} : Set K) : Subgroup K) =
      2 * m := by
    rw [hcent, Subgroup.card_map_of_injective hκinj, top_inf_eq, hC0]
  obtain ⟨s, hs⟩ : ∃ s, s = κ.range.relIndex (Subgroup.centralizer ({κ t} : Set K)) :=
    ⟨_, rfl⟩
  have hrelC : s * (2 * m) = c := by
    have := Subgroup.relIndex_mul_card κ.range (Subgroup.centralizer ({κ t} : Set K))
    rwa [hcardC, hcu, ← hs] at this
  have hsdvd : s ∣ L.index := by
    have : κ.range.Normal := hrange ▸ hLn
    have h := Subgroup.relIndex_dvd_index_of_normal κ.range
      (Subgroup.centralizer ({κ t} : Set K))
    rw [← hs, hrange] at h
    exact h
  have hsodd : Odd s := Odd.of_dvd_nat hLodd hsdvd
  have hqcases : Nat.card F = 3 ∨ Nat.card F = 5 ∨ Nat.card F = 11 ∨ Nat.card F = 13 := by
    have hdvd : s ∣ c := ⟨2 * m, hrelC.symm⟩
    have hle : s ≤ 12 := (Nat.le_of_dvd (by omega) hdvd).trans (by omega)
    obtain ⟨j, hj⟩ := hsodd
    unfold Int.ModEq at hε
    clear hsdvd hs
    interval_cases s <;> omega
  obtain ⟨p, hp, hqp⟩ : ∃ p, Nat.Prime p ∧ Nat.card F = p := by
    rcases hqcases with h | h | h | h
    · exact ⟨3, Nat.prime_three, h⟩
    · exact ⟨5, Nat.prime_five, h⟩
    · exact ⟨11, by norm_num, h⟩
    · exact ⟨13, by norm_num, h⟩
  have : Fact p.Prime := ⟨hp⟩
  have hRP : ι.range ≤ pGammaL2PGLRange F := fun x _ =>
    PGLStep.mem_pGammaL2PGLRange_of_card_prime hqp x
  have hMP : M.relIndex (pGammaL2PGLRange F) = 2 := by
    rw [hMpsl]
    exact CFSG.GorensteinWalter.pGammaL2_psl_range_relIndex_pgl_eq_two F hF
  have hR1 : M.relIndex ι.range = 1 := by
    have h1 := Subgroup.relIndex_mul_relIndex M ι.range (pGammaL2PGLRange F) hMle hRP
    rw [hMP] at h1
    have h2 : M.relIndex ι.range ∣ 2 := ⟨_, h1.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have hLtop : L = ⊤ := Subgroup.index_eq_one.mp (by rw [hLidx]; exact hR1)
  have hκsurj : Function.Surjective κ := fun y => hmemL y (hLtop ▸ Subgroup.mem_top y)
  have hs1 : s = 1 := by
    have : L.index = 1 := Subgroup.index_eq_one.mpr hLtop
    exact Nat.dvd_one.mp (this ▸ hsdvd)
  have hqfinal : ((Nat.card F = 3 ∨ Nat.card F = 5) ∧ c = 4) ∨
      ((Nat.card F = 11 ∨ Nat.card F = 13) ∧ c = 12) := by
    rw [hs1] at hrelC
    unfold Int.ModEq at hε
    omega
  let e : PSL2 F ≃* K := MulEquiv.ofBijective κ ⟨hκinj, hκsurj⟩
  have hKc : Nat.card K = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
    rw [← Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.psl2_card_formula F hF]
  rcases hqfinal with ⟨hq | hq, hc4⟩ | ⟨hq | hq, hc12⟩
  · left
    exact ⟨by rw [hKc, hq]; norm_num, hc4⟩
  · right
    left
    have : IsSimpleGroup (PSL2 F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact ⟨by rw [hKc, hq]; norm_num, e.symm.isSimpleGroup, hc4⟩
  · right
    right
    left
    exact ⟨by rw [hKc, hq]; norm_num, hc12⟩
  · right
    right
    right
    exact ⟨by rw [hKc, hq]; norm_num, hc12⟩

end Core

end PSLStep

theorem not_nine_dvd_card_of_psl_step
    {K : Type} [Group K] [Finite K]
    (hD : HasDihedralSylowTwo K)
    (h4 : 2 ^ 2 ∣ Nat.card K ∧ ¬ 2 ^ 3 ∣ Nat.card K)
    (hNC : ¬ CFSG.HasNormalPComplement 2 K) (hO : CFSG.oddCore K = ⊥)
    {u : K} (hu : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hcu : Nat.card (Subgroup.centralizer ({u} : Set K)) = 12) :
    ¬ 9 ∣ Nat.card K := by
  rcases CFSG.ABGDGroups.aSeven_or_embedding_of_hasDihedralSylowTwo hD hNC hO with
    ⟨⟨e⟩⟩ | ⟨F, _, _, hF, ι, M, hι, hM, hMle, hodd⟩
  · exact (PSLStep.false_of_mulEquiv_alternatingGroup_seven_of_not_dvd e h4.2).elim
  · rcases PSLStep.core_of_embedding hF hι hM hMle hodd h4.2 hu hu1 hcu (Or.inr rfl) with
      ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · omega
    · omega
    · rw [h]
      norm_num
    · rw [h]
      norm_num

theorem card_eq_of_psl_step_four
    {K : Type} [Group K] [Finite K]
    (hD : HasDihedralSylowTwo K)
    (h4 : 2 ^ 2 ∣ Nat.card K ∧ ¬ 2 ^ 3 ∣ Nat.card K)
    (hNC : ¬ CFSG.HasNormalPComplement 2 K) (hO : CFSG.oddCore K = ⊥)
    {u : K} (hu : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hcu : Nat.card (Subgroup.centralizer ({u} : Set K)) = 4) :
    Nat.card K = 12 ∨ (Nat.card K = 60 ∧ IsSimpleGroup K) := by
  rcases CFSG.ABGDGroups.aSeven_or_embedding_of_hasDihedralSylowTwo hD hNC hO with
    ⟨⟨e⟩⟩ | ⟨F, _, _, hF, ι, M, hι, hM, hMle, hodd⟩
  · exact (PSLStep.false_of_mulEquiv_alternatingGroup_seven_of_not_dvd e h4.2).elim
  · rcases PSLStep.core_of_embedding hF hι hM hMle hodd h4.2 hu hu1 hcu (Or.inl rfl) with
      ⟨h, -⟩ | ⟨h, hs, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, hs⟩
    · omega
    · omega

end CFSG.Sporadic.Recognition.JankoWong
