module

public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers

public section

open CFSG.GorensteinWalter (PGammaL2 PSL2 PGL2 IsOddPrimePower HasDihedralSylowTwo
  pGammaL2PSLRange pGammaL2PGLRange)

namespace CFSG.Sporadic.Recognition.JankoWong

namespace PGLStep

section General

variable {K : Type*} [Group K]

theorem commutator_le_of_index_two {J : Subgroup K} (hJ : J.index = 2) :
    commutator K ≤ J := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [commutatorElement_def]
  simp only [Subgroup.mul_mem_iff_of_index_two hJ, inv_mem_iff]
  tauto

theorem le_of_commutator_eq_self {J : Subgroup K} (hJ : J.index = 2) {A : Subgroup K}
    (hA : ⁅A, A⁆ = A) : A ≤ J := by
  rw [← hA]
  exact (Subgroup.commutator_mono le_top le_top).trans (commutator_le_of_index_two hJ)

theorem comap_commutator_eq_self {G : Type*} [Group G] {ι : K →* G}
    (hι : Function.Injective ι) {M : Subgroup G} (hMle : M ≤ ι.range) (hM : ⁅M, M⁆ = M) :
    ⁅M.comap ι, M.comap ι⁆ = M.comap ι := by
  apply Subgroup.map_injective hι
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hMle, hM]

theorem false_of_mulEquiv_alternatingGroup_seven (e : K ≃* alternatingGroup (Fin 7))
    {J : Subgroup K} (hJ : J.index = 2) (h8 : 2 ^ 3 ∣ Nat.card K) : False := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup K := e.isSimpleGroup
  have : J.Normal := Subgroup.normal_of_index_eq_two hJ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal J with h | h
  · rw [h, Subgroup.index_bot] at hJ
    rw [hJ] at h8
    norm_num at h8
  · rw [h, Subgroup.index_top] at hJ
    norm_num at hJ

theorem sylow_not_le_of_index_two [Finite K] (P : Sylow 2 K) {J : Subgroup K}
    (hJ : J.index = 2) : ¬ (P : Subgroup K) ≤ J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hle
  have h1 := Subgroup.index_dvd_of_le hle
  rw [hJ] at h1
  exact P.not_dvd_index h1

theorem exists_involution_not_mem_of_index_two [Finite K]
    (hD : HasDihedralSylowTwo K) {J : Subgroup K} (hJ : J.index = 2) :
    ∃ d : K, d ∉ J ∧ d ^ 2 = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨m, -, ⟨e⟩⟩ := hD P
  by_contra hcon
  push Not at hcon
  apply sylow_not_le_of_index_two P hJ
  let f : DihedralGroup (2 ^ m) →* K := (P : Subgroup K).subtype.comp e.symm.toMonoidHom
  have hsr : ∀ i : ZMod (2 ^ m), DihedralGroup.sr i ∈ J.comap f := by
    intro i
    by_contra hi
    refine hcon (f (DihedralGroup.sr i)) hi ?_
    rw [← map_pow, sq, DihedralGroup.sr_mul_self, map_one]
  have hall : ∀ g : DihedralGroup (2 ^ m), g ∈ J.comap f := by
    intro g
    cases g with
    | r a =>
      have : (DihedralGroup.r a : DihedralGroup (2 ^ m)) =
          DihedralGroup.sr 0 * DihedralGroup.sr a := by
        rw [DihedralGroup.sr_mul_sr, sub_zero]
      rw [this]
      exact (J.comap f).mul_mem (hsr 0) (hsr a)
    | sr a => exact hsr a
  intro y hy
  have h := hall (e ⟨y, hy⟩)
  simpa [f] using h

end General

section Prime

variable {F : Type} [Field F] [Finite F]

theorem subsingleton_ringEquiv_of_card_prime {p : ℕ} [Fact p.Prime] (hK : Nat.card F = p) :
    Subsingleton (F ≃+* F) := by
  have hord : addOrderOf (1 : F) = p := by
    have hdvd : addOrderOf (1 : F) ∣ p := hK ▸ addOrderOf_dvd_natCard (1 : F)
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h | h
    · simp at h
    · exact h
  have htop : AddSubgroup.zmultiples (1 : F) = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hord, hK]
  refine ⟨fun σ τ => ?_⟩
  ext x
  have hx : x ∈ AddSubgroup.zmultiples (1 : F) := htop ▸ AddSubgroup.mem_top x
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  simp

theorem mem_pGammaL2PGLRange_of_card_prime {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p)
    (x : PGammaL2 F) : x ∈ pGammaL2PGLRange F := by
  have := subsingleton_ringEquiv_of_card_prime hF
  have h : x.right = 1 := Subsingleton.elim _ _
  refine ⟨x.left, ?_⟩
  have := SemidirectProduct.inl_left_mul_inr_right x
  rwa [h, map_one, mul_one] at this

end Prime

section Arithmetic

theorem mod_eight_of_two_part {q : ℕ} (hq : Odd q) (h16 : ¬ 2 ^ 4 ∣ q * (q ^ 2 - 1)) :
    q % 8 = 3 ∨ q % 8 = 5 := by
  by_contra hcon
  have hmod : q % 8 = 1 ∨ q % 8 = 7 := by
    obtain ⟨k, hk⟩ := hq
    omega
  apply h16
  rcases hmod with h | h
  · obtain ⟨a, rfl⟩ : ∃ a, q = 8 * a + 1 := ⟨q / 8, by omega⟩
    have : (8 * a + 1) ^ 2 - 1 = 16 * (4 * a ^ 2 + a) := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [this]
    exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
  · obtain ⟨a, rfl⟩ : ∃ a, q = 8 * a + 7 := ⟨q / 8, by omega⟩
    have : (8 * a + 7) ^ 2 - 1 = 16 * (4 * a ^ 2 + 7 * a + 3) := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [this]
    exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _

end Arithmetic

section PGL

variable {F : Type} [Field F] [Finite F]

theorem card_centralizer_pgl2_involution (hF : IsOddPrimePower (Nat.card F)) {ε : ℤ}
    (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (hε1 : ε = 1 ∨ ε = -1) {g : PGL2 F}
    (hg : orderOf g = 2) :
    (g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ∧
        ((Nat.card (Subgroup.centralizer ({g} : Set (PGL2 F))) : ℤ) = Nat.card F - ε ∨
          (Nat.card (Subgroup.centralizer ({g} : Set (PGL2 F))) : ℤ) =
            2 * (Nat.card F - ε))) ∨
      (g ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ∧
        (Nat.card (Subgroup.centralizer ({g} : Set (PGL2 F))) : ℤ) =
          2 * (Nat.card F + ε)) := by
  classical
  set J₀ := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range with hJ₀
  have hJ₀idx : J₀.index = 2 := CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two F hF
  have hJ₀n : J₀.Normal := Subgroup.normal_of_index_eq_two hJ₀idx
  set C := Subgroup.centralizer ({g} : Set (PGL2 F)) with hC
  have hrel : J₀.relIndex C = 1 ∨ J₀.relIndex C = 2 := by
    have hdvd : J₀.relIndex C ∣ J₀.index := Subgroup.relIndex_dvd_index_of_normal J₀ C
    rw [hJ₀idx] at hdvd
    exact (Nat.dvd_prime Nat.prime_two).mp hdvd
  have hcard : J₀.relIndex C * Nat.card (J₀ ⊓ C : Subgroup (PGL2 F)) = Nat.card C :=
    Subgroup.relIndex_mul_card J₀ C
  by_cases hg₀ : g ∈ J₀
  · left
    refine ⟨hg₀, ?_⟩
    obtain ⟨t, ht⟩ := hg₀
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective t, ht, hg]
    obtain ⟨m, hm, ⟨e⟩⟩ := CFSG.ABGDGroups.psl2_centralizer_involution_dihedral hF hε hε1 ht2
    have h1 : Nat.card (J₀ ⊓ C : Subgroup (PGL2 F)) = 2 * m := by
      have hmap := CFSG.ABGDGroups.map_inf_centralizer_of_injective
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F))
        Matrix.ProjectiveSpecialLinearGroup.toPGL_injective ⊤ t
      rw [ht, ← MonoidHom.range_eq_map] at hmap
      rw [← hmap, Subgroup.card_map_of_injective
        Matrix.ProjectiveSpecialLinearGroup.toPGL_injective, top_inf_eq,
        Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    rcases hrel with h | h
    · left
      rw [h, one_mul, h1] at hcard
      rw [← hcard]
      push_cast
      linarith
    · right
      rw [h, h1] at hcard
      rw [← hcard]
      push_cast
      linarith
  · right
    refine ⟨hg₀, ?_⟩
    obtain ⟨m, hm, ⟨e⟩⟩ :=
      CFSG.ABGDGroups.pgl2_inf_centralizer_outer_involution_dihedral hF hε hε1 hg hg₀
    have h1 : Nat.card (J₀ ⊓ C : Subgroup (PGL2 F)) = 2 * m := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have h2 : J₀.relIndex C = 2 := by
      rcases hrel with h | h
      · exfalso
        exact hg₀ ((Subgroup.relIndex_eq_one.mp h) (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
      · exact h
    rw [h2, h1] at hcard
    rw [← hcard]
    push_cast
    linarith

end PGL

section Main

variable {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F]

theorem main_of_embedding (hF : IsOddPrimePower (Nat.card F)) {ι : K →* PGammaL2 F}
    (hι : Function.Injective ι) {M : Subgroup (PGammaL2 F)}
    (hM : M = pGammaL2PSLRange F ∨ M = pGammaL2PGLRange F) (hMle : M ≤ ι.range)
    (hodd : Odd (M.relIndex ι.range))
    (hD : HasDihedralSylowTwo K) (h8 : 2 ^ 3 ∣ Nat.card K ∧ ¬ 2 ^ 4 ∣ Nat.card K)
    {J : Subgroup K} (hJ : J.index = 2) {u : K} (hu : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hcu : Nat.card (Subgroup.centralizer ({u} : Set K)) = 24) :
    ∃ d r e : K, d ∉ J ∧ d ^ 2 = 1 ∧ e ^ 2 = 1 ∧ (orderOf r = 5 ∨ orderOf r = 7) ∧
      d * r = r * d ∧ d * e = e * d ∧ e * r * e⁻¹ = r⁻¹ ∧ r ∈ J ∧ e ∈ J := by
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
  have hcop : ∀ k : ℕ, Nat.Coprime (2 ^ k) L.index := fun k =>
    (Nat.coprime_two_left.mpr hLodd).pow_left k
  rcases hM with hMpsl | hMpgl
  ·
    exfalso
    have hMcard : Nat.card M = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
      rw [hMpsl, ← Nat.card_congr (CFSG.GorensteinWalter.pGammaL2PSLRangeEquiv F).toEquiv]
      exact CFSG.GorensteinWalter.psl2_card_formula F hF
    have hq3 : 3 < Nat.card F := by
      by_contra hle
      have hq3 : Nat.card F = 3 := by
        obtain ⟨k, hk⟩ := hqodd
        obtain ⟨p, f, hp, hpodd, hf, hq⟩ := hF
        have hp3 : 3 ≤ p := by
          obtain ⟨j, hj⟩ := hpodd
          have := hp.two_le
          omega
        have : p ≤ Nat.card F := by
          rw [hq]
          exact Nat.le_self_pow (by omega) p
        omega
      rw [hq3] at hMcard
      norm_num at hMcard
      have h := h8.1
      rw [← hKcard, hLcard, hMcard] at h
      have := (hcop 3).dvd_of_dvd_mul_left h
      norm_num at this
    have : Group.IsPerfect (pGammaL2PSLRange F) :=
      have := CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three F hq3
      Group.IsPerfect.range ((SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)))
    have hMperf : ⁅M, M⁆ = M := by
      rw [hMpsl]
      exact Subgroup.commutator_eq_self
    have hLJ : L ≤ J :=
      le_of_commutator_eq_self hJ (comap_commutator_eq_self hι hMle hMperf)
    have h2 := Subgroup.index_dvd_of_le hLJ
    rw [hJ] at h2
    exact (Nat.not_even_iff_odd.mpr hLodd) (even_iff_two_dvd.mpr h2)
  ·
    obtain ⟨κ, hκι⟩ : ∃ κ : PGL2 F →* K, ∀ x, ι (κ x) = SemidirectProduct.inl x := by
      have h : ∀ x : PGL2 F, ∃ k : K, ι k = SemidirectProduct.inl x := fun x =>
        hMle (by rw [hMpgl]; exact ⟨x, rfl⟩)
      choose f hf using h
      exact ⟨MonoidHom.mk' f fun a b => hι (by rw [map_mul, hf, hf, hf, map_mul]), hf⟩
    have hκinj : Function.Injective κ := fun a b hab =>
      SemidirectProduct.inl_injective (by rw [← hκι, ← hκι, hab])
    have hmemL : ∀ y ∈ L, ∃ x, κ x = y := fun y hy => by
      have hy' : ι y ∈ M := hy
      rw [hMpgl] at hy'
      obtain ⟨x, hx⟩ : ι y ∈ (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range := hy'
      exact ⟨x, hι (by rw [hκι, hx])⟩
    have hκL : ∀ x, κ x ∈ L := fun x => by
      change ι (κ x) ∈ M
      rw [hκι, hMpgl]
      exact ⟨x, rfl⟩
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
    obtain ⟨g', rfl⟩ := hmemL u huL
    have hg'2 : g' ^ 2 = 1 := hκinj (by rw [map_pow, hu, map_one])
    have hg'1 : g' ≠ 1 := fun h => hu1 (by rw [h, map_one])
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hg'ord : orderOf g' = 2 := orderOf_eq_prime hg'2 hg'1
    obtain ⟨c, hc⟩ : ∃ c, c = Nat.card (Subgroup.centralizer ({g'} : Set (PGL2 F))) :=
      ⟨_, rfl⟩
    have hcent : κ.range ⊓ Subgroup.centralizer ({κ g'} : Set K) =
        (⊤ ⊓ Subgroup.centralizer ({g'} : Set (PGL2 F))).map κ := by
      rw [CFSG.ABGDGroups.map_inf_centralizer_of_injective κ hκinj ⊤ g',
        ← MonoidHom.range_eq_map]
    have hcardC : Nat.card (κ.range ⊓ Subgroup.centralizer ({κ g'} : Set K) : Subgroup K) =
        c := by
      rw [hcent, Subgroup.card_map_of_injective hκinj, top_inf_eq, hc]
    obtain ⟨t, ht⟩ : ∃ t, t = κ.range.relIndex (Subgroup.centralizer ({κ g'} : Set K)) :=
      ⟨_, rfl⟩
    have hrelC : t * c = 24 := by
      have := Subgroup.relIndex_mul_card κ.range (Subgroup.centralizer ({κ g'} : Set K))
      rwa [hcardC, hcu, ← ht] at this
    have hrdvd : t ∣ L.index := by
      have : κ.range.Normal := hrange ▸ hLn
      have h := Subgroup.relIndex_dvd_index_of_normal κ.range
        (Subgroup.centralizer ({κ g'} : Set K))
      rw [← ht, hrange] at h
      exact h
    have htodd : Odd t := Odd.of_dvd_nat hLodd hrdvd
    have hc24 : c = 8 ∨ c = 24 := by
      have hdvd : t ∣ 24 := ⟨c, hrelC.symm⟩
      have hle : t ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
      obtain ⟨s, hs⟩ := htodd
      clear hrdvd ht
      interval_cases t <;> omega
    have hMcard : Nat.card M = Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [hMpgl, ← Nat.card_congr (CFSG.GorensteinWalter.pGammaL2PGLRangeEquiv F).toEquiv]
      exact CFSG.GorensteinWalter.pgl2_card_formula F
    have hq8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5 := by
      apply mod_eight_of_two_part hqodd
      intro h
      have h2 := h8.2
      rw [← hKcard, hLcard, hMcard] at h2
      exact h2 (Dvd.dvd.mul_left h _)
    obtain ⟨ε, hε, hε1⟩ : ∃ ε : ℤ, (Nat.card F : ℤ) ≡ ε [ZMOD 4] ∧ (ε = 1 ∨ ε = -1) := by
      obtain ⟨k, hk⟩ := hqodd
      by_cases h : Nat.card F % 4 = 1
      · exact ⟨1, by unfold Int.ModEq; omega, Or.inl rfl⟩
      · exact ⟨-1, by unfold Int.ModEq; omega, Or.inr rfl⟩
    have hcases := card_centralizer_pgl2_involution hF hε hε1 hg'ord
    rw [← hc] at hcases
    have hqcases : Nat.card F = 3 ∨ Nat.card F = 5 ∨ Nat.card F = 11 ∨ Nat.card F = 13 := by
      unfold Int.ModEq at hε
      rcases hcases with ⟨-, h | h⟩ | ⟨-, h⟩ <;> omega
    obtain ⟨p, hp, hqp⟩ : ∃ p, Nat.Prime p ∧ Nat.card F = p := by
      rcases hqcases with h | h | h | h
      · exact ⟨3, Nat.prime_three, h⟩
      · exact ⟨5, Nat.prime_five, h⟩
      · exact ⟨11, by norm_num, h⟩
      · exact ⟨13, by norm_num, h⟩
    have : Fact p.Prime := ⟨hp⟩
    have hRM : ι.range ≤ M := fun x _ => by
      rw [hMpgl]
      exact mem_pGammaL2PGLRange_of_card_prime hqp x
    have hLtop : L = ⊤ := Subgroup.index_eq_one.mp
      (by rw [hLidx]; exact Subgroup.relIndex_eq_one.mpr hRM)
    have hκsurj : Function.Surjective κ := fun y => hmemL y (hLtop ▸ Subgroup.mem_top y)
    have hrtop : κ.range = ⊤ := hrange.trans hLtop
    have ht1 : t = 1 := by rw [ht, hrtop, Subgroup.relIndex_top_left]
    have hc24' : c = 24 := by
      rw [ht1] at hrelC
      omega
    have hq1113 : Nat.card F = 11 ∨ Nat.card F = 13 := by
      unfold Int.ModEq at hε
      rcases hcases with ⟨-, h | h⟩ | ⟨-, h⟩ <;> omega
    have hq3 : 3 < Nat.card F := by omega
    have hJ'' : (J.comap κ).index = 2 := by
      rw [Subgroup.index_comap_of_surjective J hκsurj]
      exact hJ
    have hJ₀idx := CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two F hF
    have hJ₀le : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ≤
        J.comap κ := by
      rw [← CFSG.GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three F hF hq3]
      exact commutator_le_of_index_two hJ''
    have hJeq : J.comap κ =
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
      have h1 := Subgroup.relIndex_mul_index hJ₀le
      rw [hJ'', hJ₀idx] at h1
      have h2 : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.relIndex
          (J.comap κ) = 1 := by omega
      exact (Subgroup.relIndex_eq_one.mp h2).antisymm hJ₀le
    obtain ⟨d, hdJ, hd2⟩ := exists_involution_not_mem_of_index_two hD hJ
    obtain ⟨g₁, rfl⟩ := hκsurj d
    have hg₁2 : g₁ ^ 2 = 1 := hκinj (by rw [map_pow, hd2, map_one])
    have hg₁1 : g₁ ≠ 1 := fun h => hdJ (by rw [h, map_one]; exact J.one_mem)
    have hg₁ord : orderOf g₁ = 2 := orderOf_eq_prime hg₁2 hg₁1
    have hg₁J : g₁ ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
      rw [← hJeq]
      exact hdJ
    obtain ⟨m, hm, ⟨eD⟩⟩ :=
      CFSG.ABGDGroups.pgl2_inf_centralizer_outer_involution_dihedral hF hε hε1 hg₁ord hg₁J
    have hm57 : m = 5 ∨ m = 7 := by
      unfold Int.ModEq at hε
      omega
    set xr := eD.symm (DihedralGroup.r 1) with hxr
    set xe := eD.symm (DihedralGroup.sr 0) with hxe
    have hxe2 : xe ^ 2 = 1 := by
      rw [hxe, ← map_pow, sq, DihedralGroup.sr_mul_self, map_one]
    have hxrel : xe * xr * xe⁻¹ = xr⁻¹ := by
      have h : (DihedralGroup.sr 0 : DihedralGroup m) * DihedralGroup.r 1 *
          (DihedralGroup.sr 0)⁻¹ = (DihedralGroup.r 1)⁻¹ := by
        simp [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_sr,
          DihedralGroup.inv_r]
      rw [hxe, hxr, ← map_inv, ← map_mul, ← map_inv, ← map_mul, h, map_inv]
    have hxrord : orderOf xr = m := by
      rw [hxr, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    obtain ⟨hrJ₀, hrC⟩ := Subgroup.mem_inf.mp xr.2
    obtain ⟨heJ₀, heC⟩ := Subgroup.mem_inf.mp xe.2
    have hrC' : (xr : PGL2 F) * g₁ = g₁ * (xr : PGL2 F) :=
      Subgroup.mem_centralizer_singleton_iff.mp hrC
    have heC' : (xe : PGL2 F) * g₁ = g₁ * (xe : PGL2 F) :=
      Subgroup.mem_centralizer_singleton_iff.mp heC
    have hxe2' : (xe : PGL2 F) ^ 2 = 1 := by
      have := congrArg Subtype.val hxe2
      simpa using this
    have hrel' : (xe : PGL2 F) * xr * (xe : PGL2 F)⁻¹ = (xr : PGL2 F)⁻¹ := by
      have := congrArg Subtype.val hxrel
      simpa using this
    have hord' : orderOf (xr : PGL2 F) = m := by
      rw [Subgroup.orderOf_coe, hxrord]
    have hrJ : (xr : PGL2 F) ∈ J.comap κ := by
      rw [hJeq]
      exact hrJ₀
    have heJ : (xe : PGL2 F) ∈ J.comap κ := by
      rw [hJeq]
      exact heJ₀
    refine ⟨κ g₁, κ xr, κ xe, hdJ, hd2, ?_, ?_, ?_, ?_, ?_, hrJ, heJ⟩
    · rw [← map_pow, hxe2', map_one]
    · rw [orderOf_injective κ hκinj, hord']
      exact hm57
    · rw [← map_mul, ← map_mul, hrC']
    · rw [← map_mul, ← map_mul, heC']
    · have := congrArg κ hrel'
      simpa using this

end Main

end PGLStep

theorem exists_outer_involution_dihedral_centralizer
    {K : Type} [Group K] [Finite K]
    (hD : HasDihedralSylowTwo K)
    (h8 : 2 ^ 3 ∣ Nat.card K ∧ ¬ 2 ^ 4 ∣ Nat.card K)
    (hNC : ¬ CFSG.HasNormalPComplement 2 K) (hO : CFSG.oddCore K = ⊥)
    {J : Subgroup K} (hJ : J.index = 2)
    {u : K} (hu : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hcu : Nat.card (Subgroup.centralizer ({u} : Set K)) = 24) :
    ∃ d r e : K, d ∉ J ∧ d ^ 2 = 1 ∧ e ^ 2 = 1 ∧ (orderOf r = 5 ∨ orderOf r = 7) ∧
      d * r = r * d ∧ d * e = e * d ∧ e * r * e⁻¹ = r⁻¹ ∧ r ∈ J ∧ e ∈ J := by
  rcases CFSG.ABGDGroups.aSeven_or_embedding_of_hasDihedralSylowTwo hD hNC hO with
    ⟨⟨e⟩⟩ | ⟨F, _, _, hF, ι, M, hι, hM, hMle, hodd⟩
  · exact (PGLStep.false_of_mulEquiv_alternatingGroup_seven e hJ h8.1).elim
  · exact PGLStep.main_of_embedding hF hι hM hMle hodd hD h8 hJ hu hu1 hcu

end CFSG.Sporadic.Recognition.JankoWong
