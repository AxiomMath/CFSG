module

public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

open CFSG.GorensteinWalter (PGammaL2 PSL2 IsOddPrimePower HasDihedralSylowTwo
  pGammaL2PSLRange pGammaL2PGLRange)

namespace CFSG.Sporadic.Recognition.JankoWong

namespace PSLEightStep

section General

variable {K : Type*} [Group K]

theorem card_centralizer_singleton_mulEquiv {H : Type*} [Group H] (f : K ≃* H) (x : K) :
    Nat.card (Subgroup.centralizer ({f x} : Set H)) =
      Nat.card (Subgroup.centralizer ({x} : Set K)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv f.symm.toEquiv fun y => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply f.injective
    simpa using h
  · intro h
    have := congrArg f h
    simpa using this

theorem false_of_mulEquiv_alternatingGroup_seven_of_card_centralizer
    (e : K ≃* alternatingGroup (Fin 7)) {u : K} (hu : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hcu : Nat.card (Subgroup.centralizer ({u} : Set K)) = 8) : False := by
  have hev : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (e u) :=
    ⟨fun h => hu1 (e.injective (h.trans (map_one e).symm)), by rw [← map_pow, hu, map_one]⟩
  obtain ⟨g, hg⟩ := CFSG.GorensteinWalter.aSeven_involutions_conjugate (e u)
    CFSG.GorensteinWalter.a7t hev CFSG.GorensteinWalter.a7t_involution
  have h24 : Nat.card (Subgroup.centralizer ({u} : Set K)) = 24 := by
    rw [← CFSG.GorensteinWalter.a7t_centralizer_card, ← hg]
    change _ = Nat.card (Subgroup.centralizer {(MulAut.conj g) (e u)})
    rw [card_centralizer_singleton_mulEquiv, card_centralizer_singleton_mulEquiv]
  omega

end General

section Core

variable {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F]

theorem exists_index_two_of_pGLRange_le_range (hF : IsOddPrimePower (Nat.card F))
    (ι : K →* PGammaL2 F) (hMle : pGammaL2PGLRange F ≤ ι.range)
    (hodd : Odd ((pGammaL2PGLRange F).relIndex ι.range)) :
    ∃ J : Subgroup K, J.Normal ∧ J.index = 2 := by
  have hPSL : (pGammaL2PSLRange F).Normal := CFSG.ABGDGroups.pGammaL2PSLRange_normal hF
  have hN : ((pGammaL2PSLRange F).comap ι).Normal := hPSL.comap ι
  have hidx : ((pGammaL2PSLRange F).comap ι).index =
      2 * (pGammaL2PGLRange F).relIndex ι.range := by
    rw [Subgroup.index_comap, ← Subgroup.relIndex_mul_relIndex (pGammaL2PSLRange F)
      (pGammaL2PGLRange F) ι.range CFSG.ABGDGroups.pGammaL2PSLRange_le_pGLRange hMle,
      CFSG.GorensteinWalter.pGammaL2_psl_range_relIndex_pgl_eq_two F hF]
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨J, hJ, hJidx, -⟩ :=
    CFSG.GorensteinWalter.exists_normal_index_two_containing_of_index_eq_two_mul_odd hN
      (by rw [hidx]; exact dvd_mul_right _ _) (by rw [hidx, hm]; omega)
  exact ⟨J, hJ, hJidx⟩

theorem core_of_embedding_eight (hF : IsOddPrimePower (Nat.card F)) {ι : K →* PGammaL2 F}
    (hι : Function.Injective ι) {M : Subgroup (PGammaL2 F)}
    (hM : M = pGammaL2PSLRange F ∨ M = pGammaL2PGLRange F) (hMle : M ≤ ι.range)
    (hodd : Odd (M.relIndex ι.range)) (hI : ∀ J : Subgroup K, J.index ≠ 2)
    {u : K} (hu : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hcu : Nat.card (Subgroup.centralizer ({u} : Set K)) = 8) :
    Nonempty (K ≃* PSL2 F) ∧
      ((Nat.card K = 168 ∧ Nat.card F = 7) ∨
        (Nat.card K = 360 ∧ IsSimpleGroup K ∧ Nat.card F = 9)) := by
  have hMpsl : M = pGammaL2PSLRange F := by
    rcases hM with h | hMpgl
    · exact h
    · exfalso
      subst hMpgl
      obtain ⟨J, -, hJ⟩ := exists_index_two_of_pGLRange_le_range hF ι hMle hodd
      exact hI J hJ
  subst hMpsl
  have hMn : (pGammaL2PSLRange F).Normal := CFSG.ABGDGroups.pGammaL2PSLRange_normal hF
  set L := (pGammaL2PSLRange F).comap ι
  have hLn : L.Normal := hMn.comap ι
  have hLidx : L.index = (pGammaL2PSLRange F).relIndex ι.range := Subgroup.index_comap _ ι
  have hLodd : Odd L.index := hLidx ▸ hodd
  obtain ⟨κ, hκι⟩ : ∃ κ : PSL2 F →* K, ∀ x,
      ι (κ x) = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL x) := by
    have h : ∀ x : PSL2 F, ∃ k : K,
        ι k = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL x) := fun x =>
      hMle ⟨x, rfl⟩
    choose f hf using h
    exact ⟨MonoidHom.mk' f fun a b => hι (by rw [map_mul, hf, hf, hf, map_mul, map_mul]), hf⟩
  have hκinj : Function.Injective κ := fun a b hab =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      (SemidirectProduct.inl_injective (by rw [← hκι, ← hκι, hab]))
  have hmemL : ∀ y ∈ L, ∃ x, κ x = y := fun y hy => by
    have hy' : ι y ∈ pGammaL2PSLRange F := hy
    obtain ⟨x, hx⟩ := (CFSG.GorensteinWalter.mem_pGammaL2PSLRange_iff F _).mp hy'
    exact ⟨x, hι (by rw [hκι, hx])⟩
  have hκL : ∀ x, κ x ∈ L := fun x => by
    change ι (κ x) ∈ pGammaL2PSLRange F
    rw [hκι]
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
    obtain ⟨k, hk⟩ : Odd (Nat.card F) := by
      obtain ⟨p, f, -, hpodd, -, hq⟩ := hF
      rw [hq]
      exact hpodd.pow
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
  have hrelC : s * (2 * m) = 8 := by
    have := Subgroup.relIndex_mul_card κ.range (Subgroup.centralizer ({κ t} : Set K))
    rwa [hcardC, hcu, ← hs] at this
  have hsdvd : s ∣ L.index := by
    have : κ.range.Normal := hrange ▸ hLn
    have h := Subgroup.relIndex_dvd_index_of_normal κ.range
      (Subgroup.centralizer ({κ t} : Set K))
    rw [← hs, hrange] at h
    exact h
  have hsodd : Odd s := Odd.of_dvd_nat hLodd hsdvd
  have hs1 : s = 1 := by
    have hdvd : s ∣ 8 := ⟨2 * m, hrelC.symm⟩
    have hle : s ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨j, hj⟩ := hsodd
    clear hsdvd hs
    interval_cases s <;> omega
  have hqcases : Nat.card F = 7 ∨ Nat.card F = 9 := by
    rw [hs1] at hrelC
    unfold Int.ModEq at hε
    omega
  have hAut : 0 < Nat.card (F ≃+* F) ∧ Nat.card (F ≃+* F) ≤ 2 := by
    obtain ⟨p, f, hp, hpodd, hf, hqpf⟩ := hF
    have hp3 : 3 ≤ p := by
      obtain ⟨j, hj⟩ := hpodd
      have := hp.two_le
      omega
    have hf2 : f ≤ 2 := by
      by_contra hf3
      have h27 : 3 ^ 3 ≤ p ^ f :=
        (Nat.pow_le_pow_left hp3 3).trans (Nat.pow_le_pow_right hp.pos (by omega))
      rw [← hqpf] at h27
      norm_num at h27
      omega
    have hcard : Nat.card (F ≃+* F) = f :=
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp F hqpf).1
    omega
  have hRP : ι.range ≤ pGammaL2PGLRange F := by
    apply Subgroup.relIndex_eq_one.mp
    have hrodd : Odd ((pGammaL2PGLRange F).relIndex ι.range) :=
      Odd.of_dvd_nat hodd
        (Subgroup.relIndex_dvd_of_le_left ι.range CFSG.ABGDGroups.pGammaL2PSLRange_le_pGLRange)
    have h2 : (pGammaL2PGLRange F).relIndex ι.range ≤ 2 := by
      rw [CFSG.ABGDGroups.relIndex_pGLRange_eq_card_map]
      exact (Nat.le_of_dvd hAut.1 (Subgroup.card_subgroup_dvd_card _)).trans hAut.2
    obtain ⟨j, hj⟩ := hrodd
    omega
  have hMP : (pGammaL2PSLRange F).relIndex (pGammaL2PGLRange F) = 2 :=
    CFSG.GorensteinWalter.pGammaL2_psl_range_relIndex_pgl_eq_two F hF
  have hR1 : (pGammaL2PSLRange F).relIndex ι.range = 1 := by
    have h1 := Subgroup.relIndex_mul_relIndex (pGammaL2PSLRange F) ι.range
      (pGammaL2PGLRange F) hMle hRP
    rw [hMP] at h1
    have h2 : (pGammaL2PSLRange F).relIndex ι.range ∣ 2 := ⟨_, h1.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have hLtop : L = ⊤ := Subgroup.index_eq_one.mp (by rw [hLidx]; exact hR1)
  have hκsurj : Function.Surjective κ := fun y => hmemL y (hLtop ▸ Subgroup.mem_top y)
  let e : PSL2 F ≃* K := MulEquiv.ofBijective κ ⟨hκinj, hκsurj⟩
  have hKc : Nat.card K = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
    rw [← Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.psl2_card_formula F hF]
  refine ⟨⟨e.symm⟩, ?_⟩
  rcases hqcases with hq | hq
  · exact Or.inl ⟨by rw [hKc, hq]; norm_num, hq⟩
  · have : IsSimpleGroup (PSL2 F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact Or.inr ⟨by rw [hKc, hq]; norm_num, e.symm.isSimpleGroup, hq⟩

end Core

section Main

theorem exists_mulEquiv_psl_card_cases
    {K : Type} [Group K] [Finite K]
    (hD : HasDihedralSylowTwo K)
    (hNC : ¬ CFSG.HasNormalPComplement 2 K) (hO : CFSG.oddCore K = ⊥)
    (hI : ∀ M : Subgroup K, M.index ≠ 2)
    {u : K} (hu : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hcu : Nat.card (Subgroup.centralizer ({u} : Set K)) = 8) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nonempty (K ≃* PSL2 F) ∧
      ((Nat.card K = 168 ∧ Nat.card F = 7) ∨
        (Nat.card K = 360 ∧ IsSimpleGroup K ∧ Nat.card F = 9)) := by
  rcases CFSG.ABGDGroups.aSeven_or_embedding_of_hasDihedralSylowTwo hD hNC hO with
    ⟨⟨e⟩⟩ | ⟨F, _, _, hF, ι, M, hι, hM, hMle, hodd⟩
  · exact (false_of_mulEquiv_alternatingGroup_seven_of_card_centralizer e hu hu1 hcu).elim
  · exact ⟨F, inferInstance, inferInstance,
      core_of_embedding_eight hF hι hM hMle hodd hI hu hu1 hcu⟩

end Main

end PSLEightStep

theorem card_eq_of_psl_step_eight
    {K : Type} [Group K] [Finite K]
    (hD : HasDihedralSylowTwo K)
    (_h8 : 2 ^ 3 ∣ Nat.card K ∧ ¬ 2 ^ 4 ∣ Nat.card K)
    (hNC : ¬ CFSG.HasNormalPComplement 2 K) (hO : CFSG.oddCore K = ⊥)
    (hI : ∀ M : Subgroup K, M.index ≠ 2)
    {u : K} (hu : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hcu : Nat.card (Subgroup.centralizer ({u} : Set K)) = 8) :
    Nat.card K = 168 ∨ (Nat.card K = 360 ∧ IsSimpleGroup K) := by
  obtain ⟨F, _, _, -, h | ⟨h, hs, -⟩⟩ :=
    PSLEightStep.exists_mulEquiv_psl_card_cases hD hNC hO hI hu hu1 hcu
  · exact Or.inl h.1
  · exact Or.inr ⟨h, hs⟩

theorem exists_mulEquiv_psl_nine_of_psl_step_eight
    {K : Type} [Group K] [Finite K]
    (hD : HasDihedralSylowTwo K)
    (_h8 : 2 ^ 3 ∣ Nat.card K ∧ ¬ 2 ^ 4 ∣ Nat.card K)
    (hNC : ¬ CFSG.HasNormalPComplement 2 K) (hO : CFSG.oddCore K = ⊥)
    (hI : ∀ M : Subgroup K, M.index ≠ 2)
    {u : K} (hu : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hcu : Nat.card (Subgroup.centralizer ({u} : Set K)) = 8) (h360 : Nat.card K = 360) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 9 ∧ Nonempty (K ≃* PSL2 F) := by
  obtain ⟨F, _, _, hKF, ⟨h, -⟩ | ⟨-, -, h9⟩⟩ :=
    PSLEightStep.exists_mulEquiv_psl_card_cases hD hNC hO hI hu hu1 hcu
  · omega
  · exact ⟨F, inferInstance, inferInstance, h9, hKF⟩

end CFSG.Sporadic.Recognition.JankoWong
