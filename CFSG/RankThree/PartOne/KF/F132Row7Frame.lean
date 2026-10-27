module

public import CFSG.RankThree.PartOne.KF.F132Row7Data
public import CFSG.RankThree.PartOne.S13K.KF132At
public import CFSG.RankThree.PartOne.KF.F132Center
public import CFSG.RankThree.PartOne.KF.F132D8
public import CFSG.RankThree.PartOne.KFOUT3.KtyCore

public section

namespace CFSG.RankThree.PartOne.KF132

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

theorem row7_main (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hEA : E = A)
    (hG : Sec12TwoGeneric p c L E) (hf3 : 3 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ p) (ε : ↥L →* StatedProj (StatedSp 2 K)) (hε : IsCentralPQuot p ε)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (torus7 p K).map (spQ K))
    (S : D8Ctx p K L (E ⊓ L))
    (hS : ∀ d : D8Mod p K, ε (Subgroup.inclusion (inf_le_right : E ⊓ L ≤ L) (S.tor d)) =
      spQ K (torusElt p d)) :
    (∀ s ∈ reflectionSet p E, s ∈ torusImage E L → KFAt p E f s) ∧
      ∃ r₀ r₁ : MulAut E, r₀ ∈ reflectionSet p E ∧ r₀ ∈ torusImage E L ∧ r₁ ∈ reflectionSet p E ∧
        r₁ ∈ torusImage E L ∧ orderOf (r₀ * r₁) = 4 ∧
        ((kZero p E r₀).subgroupOf L).map ε = (spBlock (K := K)).range.map (spQ K) ∧
        ((kZero p E r₁).subgroupOf L).map ε = (spBlock' (K := K)).range.map (spQ K) ∧
        ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ s' ∈ reflectionSet p E,
          s' ∈ torusImage E L → orderOf (s * s') = 4 →
            ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G)),
              (s = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹ ∧
                s' = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹) ∨
              (s = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹ ∧
                s' = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹) := by
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have R : Sec12Three.Restr c L E (E ⊓ L) := h.restr_of_generic hG
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨ζ, hζ⟩
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
    calc A = E := hEA.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := hG.E_eq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  set z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p _).mpr hζp⟩ with hz
  have hz1 : z ≠ 1 := fun h1 => hζ1 (congrArg Subtype.val h1)
  have hz2 : z ^ 2 ≠ 1 := fun h1 => hz1 (eq_one_of_sq_eq_one_of_odd (hp.odd_of_ne_two hp2) h1)
  set d₀ : D8Mod p K := ((1 : rootsOfUnity p K), z) with hd₀
  set d₁ : D8Mod p K := (z, z) with hd₁
  set x₀ : G := ((S.tor d₀ : ↥(E ⊓ L)) : G) with hx₀
  set x₁ : G := ((S.tor d₁ : ↥(E ⊓ L)) : G) with hx₁
  have hx₀E : x₀ ∈ E := (S.tor d₀).2.1
  have hx₀L : x₀ ∈ L := (S.tor d₀).2.2
  have hx₁E : x₁ ∈ E := (S.tor d₁).2.1
  have hx₁L : x₁ ∈ L := (S.tor d₁).2.2
  have hb₀ : spQ K (b7 ζ) = ε ⟨x₀, hx₀L⟩ := by
    have h0 := hS d₀
    rw [torusElt_one_z] at h0
    exact h0.symm
  have hb₁ : spQ K (b7' ζ) = ε ⟨x₁, hx₁L⟩ := by
    have h0 := hS d₁
    rw [torusElt_same] at h0
    exact h0.symm
  obtain ⟨t₀, ht₀L, hr₀, hfix₀, hKF₀, hmap₀⟩ := row7_class0 hGA h hEA hcL hA hf3 hK hζ ε hε hAT
    (hEA ▸ hx₀E) hx₀L hb₀
  obtain ⟨t₁, ht₁L, hr₁, hfix₁, hKF₁, hmap₁⟩ := row7_class1 hGA h hEA hcL hA hf3 hK hζ ε hε hAT
    (hEA ▸ hx₁E) hx₁L hb₁
  have hW₀ : weylE S R hp hp2 hζex ⟨t₀, ht₀L⟩ = DihedralGroup.sr 0 :=
    weylE_eq_of_fix S R hp hp2 hζex ht₀L hr₀ (d := d₀) (i₀ := 0) (hfix₀ hx₀E)
      (fun i hi => eq_zero_of_sr_fix_one hz1 hz2 hi)
  have hW₁ : weylE S R hp hp2 hζex ⟨t₁, ht₁L⟩ = DihedralGroup.sr 3 :=
    weylE_eq_of_fix S R hp hp2 hζex ht₁L hr₁ (d := d₁) (i₀ := 3) (hfix₁ hx₁E)
      (fun i hi => eq_three_of_sr_fix_same hz2 hi)
  have hrs₀ : t₀ ∈ reflectionSet p E := ⟨hr₀, L, hF13.inZeroStar, ht₀L⟩
  have hrs₁ : t₁ ∈ reflectionSet p E := ⟨hr₁, L, hF13.inZeroStar, ht₁L⟩
  have hv0 : (0 : ZMod 4).val = 0 := rfl
  have hv3 : (3 : ZMod 4).val = 3 := rfl
  have hall : ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → KFAt p E f s := by
    intro s hs hsL
    obtain ⟨i, hi⟩ := (isAutReflection_weylE_iff S R hp hp2 hζex ⟨s, hsL⟩).1 hs.1
    have hpar : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
    rcases hpar with hpar | hpar
    · exact kfAt_of_parity S R hp hp2 hζex hW₀ hi (by rw [hv0]; omega) hKF₀
    · exact kfAt_of_parity S R hp hp2 hζex hW₁ hi (by rw [hv3]; omega) hKF₁
  refine ⟨hall, t₀, t₁, hrs₀, ht₀L, hrs₁, ht₁L, ?_, ?_, ?_, ?_⟩
  · have h1 : orderOf ((⟨t₀, ht₀L⟩ : ↥(torusImage E L)) * ⟨t₁, ht₁L⟩) = orderOf (t₀ * t₁) := by
      rw [← Subgroup.orderOf_coe]
      rfl
    rw [← h1, ← MulEquiv.orderOf_eq (weylE S R hp hp2 hζex), map_mul, hW₀, hW₁,
      DihedralGroup.sr_mul_sr, DihedralGroup.orderOf_r]
    decide
  · exact hmap₀
  · exact hmap₁
  · intro s hs hsL s' hs' hs'L hord
    obtain ⟨i, hi⟩ := (isAutReflection_weylE_iff S R hp hp2 hζex ⟨s, hsL⟩).1 hs.1
    obtain ⟨j, hj⟩ := (isAutReflection_weylE_iff S R hp hp2 hζex ⟨s', hs'L⟩).1 hs'.1
    have hne := parity_ne_of_pair S R hp hp2 hζex hi hj hord
    have hpar : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
    rcases hpar with hpar | hpar
    · obtain ⟨x, hxL, hxE, h1, h2⟩ := exists_conj_pair S R hp hp2 hζex hW₀ hW₁ hi hj
        (by rw [hv0]; omega) (by rw [hv3]; omega) hne
      exact ⟨x, hxL, hxE, Or.inl ⟨h1, h2⟩⟩
    · obtain ⟨x, hxL, hxE, h1, h2⟩ := exists_conj_pair S R hp hp2 hζex hW₁ hW₀ hi hj
        (by rw [hv3]; omega) (by rw [hv0]; omega) hne
      exact ⟨x, hxL, hxE, Or.inr ⟨h1, h2⟩⟩

theorem kf132Row7_frame (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hEA : E = A) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 2 f) :
    Subgroup.center L = ⊥ ∧
      (∀ s ∈ reflectionSet p E, s ∈ torusImage E L → KFAt p E f s) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (_ : Nat.card K = 2 ^ f)
        (ε : ↥L →* StatedProj (StatedSp 2 K)), IsCentralPQuot p ε ∧
        ∃ r₀ r₁ : MulAut E, r₀ ∈ reflectionSet p E ∧ r₀ ∈ torusImage E L ∧ r₁ ∈ reflectionSet p E ∧
          r₁ ∈ torusImage E L ∧ orderOf (r₀ * r₁) = 4 ∧
          ((kZero p E r₀).subgroupOf L).map ε = (spBlock (K := K)).range.map (spQ K) ∧
          ((kZero p E r₁).subgroupOf L).map ε = (spBlock' (K := K)).range.map (spQ K) ∧
          ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ s' ∈ reflectionSet p E,
            s' ∈ torusImage E L → orderOf (s * s') = 4 →
              ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G)),
                (s = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹ ∧
                  s' = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹) ∨
                (s = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹ ∧
                  s' = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹) := by
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hf3 := three_le_of_dvd h5 hf1 hpq
  have hZL : Subgroup.center L = ⊥ := psp_two_center_trivial hGA hf1 hF.isQuasisimple_L hmod
  have hG : Sec12TwoGeneric p c L E := sec12TwoGeneric_of_center_bot hF hZL
  have hcore : Table123Core p L (A ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h hG
  obtain ⟨K, hKf, hKfin, -, -, hK, ⟨ζ, hζ⟩, hchar, ε, hε, hFT₁, hFT₂⟩ :=
    exists_r7frame_of hcore hf1 hpq hmod
  have hAT : ((A ⊓ L).subgroupOf L).map ε = (torus7 p K).map (spQ K) := by
    have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
    rw [hAL]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  obtain ⟨S, hS⟩ := row7_S hp hp2 ⟨ζ, hζ⟩ ε hε hcore.F_le hcore.F_exp hFT₁ hFT₂
  obtain ⟨hall, hrest⟩ := row7_main hGA h hF13 hEA hG hf3 hK hζ ε hε hAT S hS
  exact ⟨hZL, hall, K, hKf, hKfin, hchar, hK, ε, hε, hrest⟩

theorem kf132Row7_data (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hEA : E = A) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 2 f) :
    (∀ s ∈ reflectionSet p E, s ∈ torusImage E L → KFAt p E f s) ∧ Subgroup.center L = ⊥ := by
  obtain ⟨hZ, hall, -⟩ := kf132Row7_frame hGA h hF hF13 hEA hf1 hpq hmod
  exact ⟨hall, hZ⟩

end CFSG.RankThree.PartOne.KF132

namespace CFSG.RankThree.PartOne.S13K

theorem kf132At_row7 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132At 7 := by
  intro G _ _ p A c L E h hF hF13 hT hr4 hrow hrA hr9 t ht htL
  have hEA : E = A := hrA (by norm_num)
  obtain ⟨f, hf1, hpq, hmod⟩ := hrow
  exact ⟨f, f, ⟨hf1, hpq, hmod⟩, rfl,
    (CFSG.RankThree.PartOne.KF132.kf132Row7_data hGA h hF hF13 hEA hf1 hpq hmod).1 t ht htL⟩

theorem kf132Types_row7 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132Types 7 :=
  kf132Types_of_at (by norm_num) (by norm_num) (by norm_num) (kf132At_row7 hGA)

end CFSG.RankThree.PartOne.S13K
