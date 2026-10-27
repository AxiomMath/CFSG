module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5110
public import CFSG.Quasithin.Vol2.Ch11SecBHBOne
public import CFSG.Quasithin.Vol2.Ch11SecB35
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAction
public import CFSG.Quasithin.Vol2.Ch11SecBHBBorel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

section Star

variable {Γ : Type} [Group Γ]

@[expose] noncomputable def starPi (M' H : Subgroup Γ) : ↥H →* E2.StarQuot M' H :=
  QuotientGroup.mk' ((kerIn M' H).subgroupOf H)

theorem starPi_surjective (M' H : Subgroup Γ) : Function.Surjective (starPi M' H) :=
  QuotientGroup.mk'_surjective _

theorem starPi_eq_one_iff {M' H : Subgroup Γ} {x : ↥H} :
    starPi M' H x = 1 ↔ (x : Γ) ∈ kerIn M' H := by
  unfold starPi
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem starPi_eq_iff {M' H : Subgroup Γ} {x y : ↥H} :
    starPi M' H x = starPi M' H y ↔ (x : Γ)⁻¹ * y ∈ kerIn M' H := by
  unfold starPi
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

theorem mem_star510_iff {M' H Y : Subgroup Γ} {y : E2.StarQuot M' H} :
    y ∈ E2.star M' H Y ↔ ∃ x : ↥H, (x : Γ) ∈ Y ∧ starPi M' H x = y := by
  unfold E2.star starPi
  rw [Subgroup.mem_map]
  simp only [Subgroup.mem_subgroupOf]

theorem starPi_mem_star {M' H Y : Subgroup Γ} {x : ↥H} (hx : (x : Γ) ∈ Y) :
    starPi M' H x ∈ E2.star M' H Y :=
  mem_star510_iff.mpr ⟨x, hx, rfl⟩

theorem map_comp_inclusion_eq_star {M' H K Y : Subgroup Γ} (hKH : K ≤ H) (hYK : Y ≤ K) :
    (Y.subgroupOf K).map ((starPi M' H).comp (Subgroup.inclusion hKH)) = E2.star M' H Y := by
  ext y
  rw [mem_star510_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Subgroup.inclusion hKH x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hYK hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem range_comp_inclusion_eq_star {M' H K : Subgroup Γ} (hKH : K ≤ H) :
    ((starPi M' H).comp (Subgroup.inclusion hKH)).range = E2.star M' H K := by
  rw [MonoidHom.range_eq_map, ← map_comp_inclusion_eq_star hKH le_rfl, Subgroup.subgroupOf_self]

@[expose] noncomputable def starRes (M' H K : Subgroup Γ) (hKH : K ≤ H) :
    ↥K →* ↥(E2.star M' H K) :=
  ((starPi M' H).comp (Subgroup.inclusion hKH)).codRestrict (E2.star M' H K) fun k =>
    starPi_mem_star (x := Subgroup.inclusion hKH k) k.2

theorem starRes_surjective {M' H K : Subgroup Γ} (hKH : K ≤ H) :
    Function.Surjective (starRes M' H K hKH) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := mem_star510_iff.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

theorem starRes_eq_one_iff {M' H K : Subgroup Γ} (hKH : K ≤ H) {k : ↥K} :
    starRes M' H K hKH k = 1 ↔ (k : Γ) ∈ kerIn M' H := by
  have h := starPi_eq_one_iff (M' := M') (x := Subgroup.inclusion hKH k)
  exact ⟨fun h1 => h.mp (congrArg Subtype.val h1), fun h1 => Subtype.ext (h.mpr h1)⟩

theorem starPi_mem_normalizer {M' H Y : Subgroup Γ} {h : ↥H}
    (hY : (h : Γ) ∈ Subgroup.normalizer (Y : Set Γ)) :
    starPi M' H h ∈
      Subgroup.normalizer ((E2.star M' H Y : Subgroup _) : Set (E2.StarQuot M' H)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_star510_iff.mp hy
    refine mem_star510_iff.mpr ⟨h * x * h⁻¹, ?_, by simp [map_mul, map_inv]⟩
    simpa using (Subgroup.mem_normalizer_iff.mp hY _).mp hx
  · intro hy
    obtain ⟨x, hx, hxy⟩ := mem_star510_iff.mp hy
    refine mem_star510_iff.mpr ⟨h⁻¹ * x * h, ?_, ?_⟩
    · have h1 : (h : Γ) * ((h : Γ)⁻¹ * x * h) * (h : Γ)⁻¹ ∈ Y := by simpa [mul_assoc] using hx
      simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.mp hY _).mpr h1
    · rw [map_mul, map_mul, map_inv, hxy]
      group

variable [Finite Γ] in
theorem mem_normalizer_of_conj_mem' {A : Subgroup Γ} {g : Γ} (h : ∀ a ∈ A, g * a * g⁻¹ ∈ A) :
    g ∈ Subgroup.normalizer (A : Set Γ) := by
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  have heq : A.map (MulAut.conj g).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  exact A38.map_conj_eq_iff.mp heq

end Star

variable {G : Type} [Group G] [Finite G]

structure Set510 (G : Type) [Group G] [Finite G] (T M L H B D K : Subgroup G) (n k : ℕ) :
    Prop where
  hyp : Hyp5_1_8 G T M L H n
  nota : IsNotation5_1_9 T M L H B D
  comp : K ∈ cComp H
  sup : H = K ⊔ T
  quasi : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)
  cases : E22FieldCases H T (H ⊓ M) K k

namespace Set510

variable {T M L H B D K : Subgroup G} {n k : ℕ} (s : Set510 G T M L H B D K n k)
include s

theorem T_le_H : T ≤ H := s.hyp.hStar.1.1

theorem T_le_M : T ≤ M := s.hyp.T_le

theorem T_le_X : T ≤ H ⊓ M := le_inf s.T_le_H s.T_le_M

theorem K_le_H : K ≤ H := le_of_mem_cComp s.comp

theorem sylowH : IsSylowTwoOf T H := s.hyp.toHyp5_0_1.isSylowTwoOf s.T_le_H

theorem isPGroup_T : IsPGroup 2 T := s.sylowH.2.1

theorem sylowK : IsSylowTwoOf (T ⊓ K) K :=
  A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp s.comp) s.sylowH

theorem perfect : ⁅K, K⁆ = K := perfect_of_mem_cComp s.comp

theorem uniqueMax : IsUniqueMaxOver H T (H ⊓ M) := by
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq s.hyp.sylow
  exact s.hyp.hStar.isUniqueMaxOver S s.hyp.T_le

theorem not_le_M : ¬ H ≤ M := s.hyp.hStar.2.1

theorem two_le_k : 2 ≤ k := by
  have hc := s.cases
  dsimp only [E22FieldCases] at hc
  rcases hc with ⟨-, -, -, -, -, hk, -⟩ | ⟨-, -, ⟨hBen, -⟩ | ⟨hk, -⟩⟩
  · exact hk
  · exact hBen.1
  · exact hk

theorem pCoreOf_le_T : pCoreOf 2 H ≤ T :=
  s.sylowH.le_of_normalizes (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
    (have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
     CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)

theorem pCoreOf_le_kerIn : pCoreOf 2 H ≤ kerIn (H ⊓ M) H := by
  intro x hx
  rw [mem_kerIn]
  intro b hb
  have h1 : b * x * b⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hb) x).mp hx
  exact s.T_le_X (s.pCoreOf_le_T h1)

theorem pCoreOf_K_le : pCoreOf 2 K ≤ T ⊓ K :=
  s.sylowK.le_of_normalizes (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
    (have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
     CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)

theorem inf_pCoreOf_le : K ⊓ pCoreOf 2 H ≤ T ⊓ K :=
  (Vol2.Ch11.SecB.inf_pCoreOf_le_pCoreOf s.K_le_H).trans s.pCoreOf_K_le

theorem oTwoUpper_eq : oTwoUpper H = conjClosure K T := by
  rw [Vol2.Ch11.SecB.oTwoUpper_eq_conjClosure s.perfect s.isPGroup_T s.sup]
  refine le_antisymm (conjClosure_le fun h hh k hk => ?_) (conjClosure_mono le_rfl s.T_le_H)
  have hN : H ≤ Subgroup.normalizer (conjClosure K T : Set G) := by
    rw [s.sup]
    exact sup_le (fun k hk => Subgroup.le_normalizer (le_conjClosure K T hk))
      (le_normalizer_conjClosure K T)
  exact (Subgroup.mem_normalizer_iff.mp (hN hh) k).mp (le_conjClosure K T hk)

theorem K_le_oTwoUpper : K ≤ oTwoUpper H := s.oTwoUpper_eq ▸ le_conjClosure K T

theorem sylowR : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
  A4.isSylowTwoOf_inf_normal s.sylowH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)

theorem isBorelIn_star :
    E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)) := by
  have hc := s.cases
  dsimp only [E22FieldCases] at hc
  rcases hc with ⟨-, -, -, -, -, -, -, hB⟩ | ⟨-, -, ⟨-, hB⟩ | ⟨-, -, -, hB⟩⟩
  · exact hB
  · exact hB
  · exact hB

theorem sylowKs : IsSylowTwoOf (E2.star (H ⊓ M) H (T ⊓ K)) (E2.star (H ⊓ M) H K) := by
  have h := Setup.Family.isSylowTwoOf_map_range
    ((starPi (H ⊓ M) H).comp (Subgroup.inclusion s.K_le_H)) s.sylowK
  rwa [map_comp_inclusion_eq_star s.K_le_H inf_le_right,
    range_comp_inclusion_eq_star s.K_le_H] at h

theorem borel_eq : E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K) = E2.star (H ⊓ M) H K ⊓
    Subgroup.normalizer ((E2.star (H ⊓ M) H (T ⊓ K) : Subgroup (E2.StarQuot (H ⊓ M) H)) :
      Set (E2.StarQuot (H ⊓ M) H)) := by
  obtain ⟨S', hS', hB⟩ := s.isBorelIn_star
  have hTs := s.sylowKs
  have hTM : E2.star (H ⊓ M) H (T ⊓ K) ≤ E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K) :=
    Subgroup.map_mono fun x hx => (inf_le_inf_right K s.T_le_X : T ⊓ K ≤ _) hx
  have hTN : E2.star (H ⊓ M) H (T ⊓ K) ≤ Subgroup.normalizer (S' : Set _) :=
    hTM.trans (hB ▸ inf_le_right)
  have h2 := IsPGroup.to_sup_of_normal_right' hTs.2.1 hS'.2.1 hTN
  have heq := hS'.eq_of_le le_sup_right (sup_le hTs.1 hS'.1) h2
  have hTS : E2.star (H ⊓ M) H (T ⊓ K) ≤ S' := heq ▸ le_sup_left
  have hS'eq := hTs.eq_of_le hTS hS'.1 hS'.2.1
  rw [hB, hS'eq]

theorem exists_conj_of_normalizer {m : G} {hmH : m ∈ H}
    (hmN : starPi (H ⊓ M) H ⟨m, hmH⟩ ∈ Subgroup.normalizer
      ((E2.star (H ⊓ M) H (T ⊓ K) : Subgroup (E2.StarQuot (H ⊓ M) H)) :
        Set (E2.StarQuot (H ⊓ M) H)))
    {x : G} (hx : x ∈ T ⊓ K) :
    ∃ y ∈ T ⊓ K, y⁻¹ * (m * x * m⁻¹) ∈ kerIn (H ⊓ M) H := by
  have hxH : x ∈ H := s.T_le_H hx.1
  have hx' : starPi (H ⊓ M) H ⟨x, hxH⟩ ∈ E2.star (H ⊓ M) H (T ⊓ K) := starPi_mem_star hx
  have h1 := (Subgroup.mem_normalizer_iff.mp hmN _).mp hx'
  rw [← map_mul, ← map_inv, ← map_mul] at h1
  obtain ⟨y, hy, hyx⟩ := mem_star510_iff.mp h1
  refine ⟨y, hy, ?_⟩
  have h2 := starPi_eq_iff.mp hyx
  simpa using h2

theorem mem_normalizer_of_starPi
    (hJK : ∀ j ∈ K, j ∈ kerIn (H ⊓ M) H → ∀ x ∈ T ⊓ K, j * x * j⁻¹ ∈ T ⊓ K)
    {m : G} (hmK : m ∈ K)
    (hmN : starPi (H ⊓ M) H ⟨m, s.K_le_H hmK⟩ ∈ Subgroup.normalizer
      ((E2.star (H ⊓ M) H (T ⊓ K) : Subgroup (E2.StarQuot (H ⊓ M) H)) :
        Set (E2.StarQuot (H ⊓ M) H))) :
    m ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJN : ∀ j ∈ K, j ∈ kerIn (H ⊓ M) H →
      j ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    intro j hjK hjJ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hJK j hjK hjJ x, fun hx => ?_⟩
    have h1 := hJK j⁻¹ (K.inv_mem hjK) ((kerIn (H ⊓ M) H).inv_mem hjJ) _ hx
    simpa [mul_assoc] using h1
  set P := (T ⊓ K).map (MulAut.conj m).toMonoidHom with hP
  have hPK : P ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact K.mul_mem (K.mul_mem hmK hx.2) (K.inv_mem hmK)
  have hP2 : IsPGroup 2 P := s.sylowK.2.1.map _
  have hPN : P ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyJ⟩ := s.exists_conj_of_normalizer hmN hx
    have hc : (MulAut.conj m).toMonoidHom x = m * x * m⁻¹ := rfl
    rw [hc]
    have hyK : y⁻¹ * (m * x * m⁻¹) ∈ K :=
      K.mul_mem (K.inv_mem hy.2) (K.mul_mem (K.mul_mem hmK hx.2) (K.inv_mem hmK))
    have h1 := hJN _ hyK hyJ
    have h2 : y ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := Subgroup.le_normalizer hy
    have := Subgroup.mul_mem _ h2 h1
    simpa using this
  have h2 := IsPGroup.to_sup_of_normal_right' hP2 s.sylowK.2.1 hPN
  have heq := s.sylowK.eq_of_le le_sup_right (sup_le hPK s.sylowK.1) h2
  have hPle : P ≤ T ⊓ K := heq ▸ le_sup_left
  have hPeq : P = T ⊓ K := by
    refine Subgroup.eq_of_le_of_card_ge hPle ?_
    rw [hP, Subgroup.card_map_of_injective (MulAut.conj m).injective]
  exact A38.map_conj_eq_iff.mp hPeq

theorem inf_le_normalizer
    (hJK : ∀ j ∈ K, j ∈ kerIn (H ⊓ M) H → ∀ x ∈ T ⊓ K, j * x * j⁻¹ ∈ T ⊓ K) :
    (H ⊓ M) ⊓ K ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  intro m hm
  have hm' : starPi (H ⊓ M) H ⟨m, s.K_le_H hm.2⟩ ∈ E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K) :=
    starPi_mem_star hm
  rw [s.borel_eq] at hm'
  exact s.mem_normalizer_of_starPi hJK hm.2 hm'.2

theorem normalizer_inf_le :
    oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) ≤ M := by
  set R := oTwoUpper H with hR
  set Y := H ⊓ Subgroup.normalizer ((T ⊓ R : Subgroup G) : Set G) with hY
  have hTY : T ≤ Y := le_inf s.T_le_H fun t ht => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have htR : t ∈ Subgroup.normalizer (R : Set G) := le_normalizer_oTwoUpper H (s.T_le_H ht)
    constructor
    · rintro ⟨hxT, hxR⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht),
        (Subgroup.mem_normalizer_iff.mp htR x).mp hxR⟩
    · rintro ⟨hxT, hxR⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp htR x).mpr hxR⟩
      have := T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
      simpa [mul_assoc] using this
  rcases eq_or_lt_of_le (inf_le_left : Y ≤ H) with hYH | hYH
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hHN : H ≤ Subgroup.normalizer ((T ⊓ R : Subgroup G) : Set G) := hYH ▸ inf_le_right
    have hTRO : T ⊓ R ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_right.trans (oTwoUpper_le H))
        hHN (s.isPGroup_T.to_le inf_le_left)
    have hTKJ : T ⊓ K ≤ kerIn (H ⊓ M) H :=
      (inf_le_inf_left T s.K_le_oTwoUpper).trans (hTRO.trans s.pCoreOf_le_kerIn)
    have hbot : E2.star (H ⊓ M) H (T ⊓ K) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_star510_iff.mp hy
      exact starPi_eq_one_iff.mpr (hTKJ hx)
    have hMK := s.borel_eq
    rw [hbot] at hMK
    have hKM : K ≤ M := by
      intro k hk
      have hk' : starPi (H ⊓ M) H ⟨k, s.K_le_H hk⟩ ∈ E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K) := by
        have hN : starPi (H ⊓ M) H ⟨k, s.K_le_H hk⟩ ∈ Subgroup.normalizer
            (((⊥ : Subgroup (E2.StarQuot (H ⊓ M) H)) : Set (E2.StarQuot (H ⊓ M) H))) := by
          rw [Subgroup.mem_normalizer_iff]
          intro w
          simp only [Subgroup.mem_bot]
          constructor
          · intro h
            rw [h]
            group
          · intro h
            have h1 := mul_inv_eq_one.mp h
            simpa using h1
        rw [hMK]
        exact ⟨starPi_mem_star hk, hN⟩
      obtain ⟨m, hm, hmk⟩ := mem_star510_iff.mp hk'
      have h1 := kerIn_le (starPi_eq_iff.mp hmk)
      have h2 : (m : G) * ((m : G)⁻¹ * k) ∈ H ⊓ M := (H ⊓ M).mul_mem hm.1 h1
      simpa using h2.2
    exact s.not_le_M (s.sup ▸ sup_le hKM s.T_le_M)
  · have hYX : Y ≤ H ⊓ M := Vol2.Ch11.SecB.le_of_isUniqueMaxOver s.uniqueMax hTY hYH
    intro x hx
    exact (hYX ⟨oTwoUpper_le H hx.1, hx.2⟩).2

theorem isBorelIn_of
    (hX : H ⊓ M ⊓ oTwoUpper H ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G)) :
    E2.IsBorelIn (oTwoUpper H) (M ⊓ oTwoUpper H) := by
  refine ⟨T ⊓ oTwoUpper H, s.sylowR, le_antisymm ?_ ?_⟩
  · intro x hx
    exact ⟨hx.2, hX ⟨⟨oTwoUpper_le H hx.2, hx.1⟩, hx.2⟩⟩
  · intro x hx
    exact ⟨s.normalizer_inf_le hx, hx.1⟩

end Set510

end CFSG.Quasithin.H13
