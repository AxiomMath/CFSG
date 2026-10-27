module

public import CFSG.RankThree.PartTwo.J2Residue.Config
public import CFSG.RankThree.PartTwo.Sec3.Item321
public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L LB : Subgroup G} {d : G}

private theorem tripleCover_card_data {T : Type*} [Group T] [Finite T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) :
    Nat.card (Subgroup.center T) = 3 ∧ Nat.card (T ⧸ Subgroup.center T) = 360 ∧
      Nat.card T = 1080 := by
  obtain ⟨hZ, ⟨e⟩⟩ := hT
  have hQ : Nat.card (T ⧸ Subgroup.center T) = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hTcard : Nat.card T = 1080 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center T)
    rw [hZ, hQ] at h
    omega
  exact ⟨hZ, hQ, hTcard⟩

private theorem tripleCover_normal_le_center_or_sup_eq_top {T : Type*} [Group T] [Finite T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) {K : Subgroup T}
    (hK : K.Normal) :
    K ≤ Subgroup.center T ∨ K ⊔ Subgroup.center T = ⊤ := by
  obtain ⟨-, hQ, -⟩ := tripleCover_card_data hT
  obtain ⟨e⟩ := hT.2
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup (T ⧸ Subgroup.center T) := MulEquiv.isSimpleGroup e
  have hnorm : (K.map (QuotientGroup.mk' (Subgroup.center T))).Normal :=
    Subgroup.Normal.map hK _ (QuotientGroup.mk'_surjective _)
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (K.map (QuotientGroup.mk' (Subgroup.center T))) with h | h
  · left
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · right
    rw [eq_top_iff]
    intro x _
    have hx : QuotientGroup.mk' (Subgroup.center T) x ∈
        K.map (QuotientGroup.mk' (Subgroup.center T)) := by
      rw [h]; exact Subgroup.mem_top _
    obtain ⟨k, hkK, hkx⟩ := Subgroup.mem_map.mp hx
    have hker : k⁻¹ * x ∈ Subgroup.center T := by
      rw [← QuotientGroup.eq_one_iff (N := Subgroup.center T)]
      change QuotientGroup.mk' (Subgroup.center T) (k⁻¹ * x) = 1
      rw [map_mul, map_inv, hkx, inv_mul_cancel]
    have hxeq : x = k * (k⁻¹ * x) := by group
    rw [hxeq]
    exact Subgroup.mul_mem_sup hkK hker

private theorem tripleCover_eq_top_of_sup_center {T : Type*} [Group T] [Finite T]
    (hperf : Group.IsPerfect T) {K : Subgroup T} (hK : K.Normal)
    (hsup : K ⊔ Subgroup.center T = ⊤) : K = ⊤ := by
  rw [eq_top_iff, ← hperf.commutator_eq_top, _root_.commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨c₁, hc₁, z₁, hz₁, rfl⟩ :=
    Subgroup.mem_sup_of_normal_right.mp (hsup ▸ Subgroup.mem_top x)
  obtain ⟨c₂, hc₂, z₂, hz₂, rfl⟩ :=
    Subgroup.mem_sup_of_normal_right.mp (hsup ▸ Subgroup.mem_top y)
  have h1 : ∀ g : T, z₁ * g = g * z₁ := fun g => (Subgroup.mem_center_iff.mp hz₁ g).symm
  have h2 : ∀ g : T, z₂ * g = g * z₂ := fun g => (Subgroup.mem_center_iff.mp hz₂ g).symm
  rw [commutatorElement_def]
  have hA : c₁ * z₁ * (c₂ * z₂) = c₁ * c₂ * (z₁ * z₂) :=
    Commute.mul_mul_mul_comm (h1 c₂) c₁ z₂
  have hB : c₂ * z₂ * (c₁ * z₁) = c₂ * c₁ * (z₂ * z₁) :=
    Commute.mul_mul_mul_comm (h2 c₁) c₂ z₁
  have hz : z₁ * z₂ = z₂ * z₁ := h1 z₂
  have hcalc : c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹ =
      c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by
    calc c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹ =
        (c₁ * z₁ * (c₂ * z₂)) * (c₂ * z₂ * (c₁ * z₁))⁻¹ := by group
      _ = (c₁ * c₂ * (z₁ * z₂)) * (c₂ * c₁ * (z₂ * z₁))⁻¹ := by rw [hA, hB]
      _ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by rw [hz]; group
  rw [hcalc]
  exact K.mul_mem (K.mul_mem (K.mul_mem hc₁ hc₂) (K.inv_mem hc₁)) (K.inv_mem hc₂)

private theorem tripleCover_cube_mem_center {T : Type*} [Group T] [Finite T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    {S : Subgroup T} (hScard : Nat.card S = 27) {y : T} (hy : y ∈ S) :
    y ^ 3 ∈ Subgroup.center T := by
  obtain ⟨hZcard, hQcard, -⟩ := tripleCover_card_data hT
  obtain ⟨e⟩ := hT.2
  have hno9 : ∀ z : T ⧸ Subgroup.center T, orderOf z ≠ 9 := by
    intro z hz
    have hz' : orderOf (e z) = 9 := by rw [MulEquiv.orderOf_eq, hz]
    let σ : alternatingGroup (Fin 6) := e z
    have hσ : orderOf (σ : Equiv.Perm (Fin 6)) = 9 := by
      rw [Subgroup.orderOf_coe]
      exact hz'
    have hσ9 : orderOf σ ≠ 9 := by
      intro h
      have hperm : orderOf (σ : Equiv.Perm (Fin 6)) ≠ 9 := by
        intro h'
        have hlcm : (σ : Equiv.Perm (Fin 6)).cycleType.lcm = 9 := by
          rw [Equiv.Perm.lcm_cycleType, h']
        have h3 : ∀ c ∈ (σ : Equiv.Perm (Fin 6)).cycleType, c = 3 := by
          intro c hc
          have hcdvd : c ∣ 9 := by
            rw [← h']
            exact Equiv.Perm.dvd_of_mem_cycleType hc
          have hc2 := Equiv.Perm.two_le_of_mem_cycleType hc
          have hc6 : c ≤ 6 := by
            have h1 : c ≤ (σ : Equiv.Perm (Fin 6)).cycleType.sum :=
              Multiset.single_le_sum (fun _ _ => Nat.zero_le _) c hc
            have h2 : (σ : Equiv.Perm (Fin 6)).cycleType.sum ≤ Fintype.card (Fin 6) :=
              Equiv.Perm.sum_cycleType_le (σ : Equiv.Perm (Fin 6))
            simpa using h1.trans h2
          have hcdvd' : c ∣ 3 ^ 2 := by simpa using hcdvd
          obtain ⟨j, hjle, hj⟩ :=
            (Nat.dvd_prime_pow (p := 3) (m := 2) Nat.prime_three).mp hcdvd'
          interval_cases j <;> simp_all
        have hdvd3 : (σ : Equiv.Perm (Fin 6)).cycleType.lcm ∣ 3 :=
          Multiset.lcm_dvd.mpr fun c hc => by rw [h3 c hc]
        rw [hlcm] at hdvd3
        norm_num at hdvd3
      exact hperm hσ
    exact hσ9 hz'
  have hordS : orderOf y ∣ 27 := by
    have := Subgroup.orderOf_dvd_natCard S hy
    rwa [hScard] at this
  have hdiv27 : orderOf (QuotientGroup.mk' (Subgroup.center T) y) ∣ 27 :=
    (orderOf_map_dvd _ y).trans hordS
  have hdiv360 : orderOf (QuotientGroup.mk' (Subgroup.center T) y) ∣ 360 := by
    have := orderOf_dvd_natCard (QuotientGroup.mk' (Subgroup.center T) y)
    rwa [hQcard] at this
  have hdiv9 : orderOf (QuotientGroup.mk' (Subgroup.center T) y) ∣ 9 := by
    have := Nat.dvd_gcd hdiv27 hdiv360
    rwa [show Nat.gcd 27 360 = 9 by norm_num] at this
  have hdiv9' : orderOf (QuotientGroup.mk' (Subgroup.center T) y) ∣ 3 ^ 2 := by
    simpa using hdiv9
  have hdiv3 : orderOf (QuotientGroup.mk' (Subgroup.center T) y) ∣ 3 := by
    obtain ⟨j, hjle, hj⟩ :=
      (Nat.dvd_prime_pow (p := 3) (m := 2) Nat.prime_three).mp hdiv9'
    interval_cases j
    · rw [hj]; norm_num
    · rw [hj]; norm_num
    · exfalso
      exact hno9 _ (by rw [hj]; norm_num)
  rw [← QuotientGroup.eq_one_iff (N := Subgroup.center T)]
  change QuotientGroup.mk' (Subgroup.center T) (y ^ 3) = 1
  rw [map_pow]
  exact orderOf_dvd_iff_pow_eq_one.mp hdiv3

omit [Finite G] in
theorem J2Config.lB_le (h : J2Config L d LB) :
    LB ≤ L ⊓ Subgroup.centralizer ({d} : Set G) := by
  rw [h.lB_eq]
  exact Subgroup.map_subtype_le _

theorem J2Config.isPerfect_lB (h : J2Config L d LB) : Group.IsPerfect LB := by
  rw [h.lB_eq]
  exact CFSG.SignalizerFunctorTheorem.Nonsolvable.isPerfect_perfectResidual_map _

theorem J2Config.lB_inf_pCoreOf (h : J2Config L d LB) :
    LB ⊓ CFSG.Open.pCoreOf 2 L = CFSG.Open.pCoreOf 2 LB := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ ?_
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
    · refine (le_inf Subgroup.le_normalizer ?_).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := LB)
          (K := CFSG.Open.pCoreOf 2 L))
      exact (h.lB_le.trans inf_le_left).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_right
  · exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 LB) h.pCoreOf_le

theorem J2Config.commutator_le (h : J2Config L d LB) :
    ⁅CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G), LB⁆ ≤
      CFSG.Open.pCoreOf 2 LB := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup G := CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G)
  have hWnormX : W ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer ({d} : Set G)) : Set G) := by
    refine (le_inf ?_ ?_).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := L)
        (K := Subgroup.centralizer ({d} : Set G)))
    · exact (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).trans
        Subgroup.le_normalizer
    · exact inf_le_right.trans Subgroup.le_normalizer
  have hWnormLB : W ≤ Subgroup.normalizer (LB : Set G) := by
    rw [h.lB_eq]
    have hres := CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_le_normalizer_perfectResidual_map
      (L ⊓ Subgroup.centralizer ({d} : Set G))
    change Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({d} : Set G)) : Set G) ≤
      Subgroup.normalizer
        (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) : Set G) at hres
    exact hWnormX.trans hres
  have h1 : ⁅W, LB⁆ ≤ LB := by
    rw [Subgroup.commutator_le]
    intro w hw b hb
    have hwb : w * b * w⁻¹ ∈ LB :=
      (Subgroup.mem_normalizer_iff.mp (hWnormLB hw) b).mp hb
    rw [commutatorElement_def]
    have : w * b * w⁻¹ * b⁻¹ = (w * b * w⁻¹) * b⁻¹ := by group
    rw [this]
    exact LB.mul_mem hwb (LB.inv_mem hb)
  have h2 : ⁅W, LB⁆ ≤ CFSG.Open.pCoreOf 2 L := by
    rw [Subgroup.commutator_le]
    intro w hw b hb
    have hwO : w ∈ CFSG.Open.pCoreOf 2 L := hw.1
    have hbL : b ∈ L := (h.lB_le hb).1
    have hbn : b ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) hbL
    have hconj : b * w⁻¹ * b⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp hbn (w⁻¹)).mp
        ((CFSG.Open.pCoreOf 2 L).inv_mem hwO)
    rw [commutatorElement_def]
    have : w * b * w⁻¹ * b⁻¹ = w * (b * w⁻¹ * b⁻¹) := by group
    rw [this]
    exact (CFSG.Open.pCoreOf 2 L).mul_mem hwO hconj
  have hle : ⁅W, LB⁆ ≤ LB ⊓ CFSG.Open.pCoreOf 2 L := le_inf h1 h2
  rwa [h.lB_inf_pCoreOf] at hle

theorem J2Config.normalizer_le (h : J2Config L d LB) :
    L ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤ Subgroup.normalizer (LB : Set G) := by
  have hcent : Subgroup.centralizer (Subgroup.zpowers d : Set G) =
      Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hH : L ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤
      Subgroup.normalizer (L : Set G) ⊓
        Subgroup.normalizer (Subgroup.centralizer ({d} : Set G) : Set G) := by
    refine le_inf (inf_le_left.trans Subgroup.le_normalizer) ?_
    refine (inf_le_right.trans ?_)
    simpa [hcent] using
      CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer
        (Subgroup.zpowers d)
  have hH' : L ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤
      Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({d} : Set G)) : Set G) :=
    hH.trans (Subgroup.inf_normalizer_le_normalizer_inf (H := L)
      (K := Subgroup.centralizer ({d} : Set G)))
  rw [h.lB_eq]
  have hres := CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_le_normalizer_perfectResidual_map
    (L ⊓ Subgroup.centralizer ({d} : Set G))
  change Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({d} : Set G)) : Set G) ≤
    Subgroup.normalizer
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) : Set G) at hres
  exact hH'.trans hres

theorem J2Config.inf_le_pCoreOf (h : J2Config L d LB) {N : Subgroup G}
    (hN : LB ≤ Subgroup.normalizer (N : Set G)) (hN3 : ¬ 3 ∣ Nat.card N) :
    N ⊓ LB ≤ CFSG.Open.pCoreOf 2 LB := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T := ↥LB ⧸ CFSG.pCore 2 ↥LB
  let π : ↥LB →* T := QuotientGroup.mk' _
  let M : Subgroup G := N ⊓ LB
  change M ≤ CFSG.Open.pCoreOf 2 LB
  have hMLB : M ≤ LB := inf_le_right
  have hMnorm : LB ≤ Subgroup.normalizer (M : Set G) := by
    refine (le_inf hN ?_).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := N) (K := LB))
    exact Subgroup.le_normalizer
  have hMLnorm : (M.subgroupOf LB).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMLB).mpr hMnorm
  let K : Subgroup T := (M.subgroupOf LB).map π
  have hKnorm : K.Normal := Subgroup.Normal.map hMLnorm π (QuotientGroup.mk'_surjective _)
  have hK3 : ¬ 3 ∣ Nat.card K := by
    intro h3
    apply hN3
    have hKdvdN : Nat.card K ∣ Nat.card N := by
      have h1 : Nat.card K ∣ Nat.card (M.subgroupOf LB) := Subgroup.card_map_dvd _ π
      have h2 : Nat.card (M.subgroupOf LB) = Nat.card M :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMLB).toEquiv
      rw [h2] at h1
      exact h1.trans (Subgroup.card_dvd_of_le inf_le_left)
    exact h3.trans hKdvdN
  have hKbot : K = ⊥ := by
    rcases tripleCover_normal_le_center_or_sup_eq_top h.tripleCover hKnorm with hKZ | hKsup
    · have hZcard := (tripleCover_card_data h.tripleCover).1
      have hKdvd3 : Nat.card K ∣ 3 := by
        have := Subgroup.card_dvd_of_le hKZ
        rwa [hZcard] at this
      have hKcard1 : Nat.card K = 1 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hKdvd3 with h1 | h1
        · exact h1
        · rw [h1] at hK3
          exact absurd dvd_rfl hK3
      exact Subgroup.card_eq_one.mp hKcard1
    · have hZcard := (tripleCover_card_data h.tripleCover).1
      have hQcard := (tripleCover_card_data h.tripleCover).2.1
      let f : K →* T ⧸ Subgroup.center T :=
        (QuotientGroup.mk' (Subgroup.center T)).comp K.subtype
      have hfker_eq : f.ker = (Subgroup.center T).comap K.subtype := by
        change ((QuotientGroup.mk' (Subgroup.center T)).comp K.subtype).ker =
          (Subgroup.center T).comap K.subtype
        rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      have hfker_dvd_Z : Nat.card f.ker ∣ Nat.card (Subgroup.center T) := by
        rw [hfker_eq]
        exact Subgroup.card_comap_dvd_of_injective _ _ K.subtype_injective
      have hfker_dvd_K : Nat.card f.ker ∣ Nat.card K := by
        have := Subgroup.card_dvd_of_le (H := f.ker) (K := ⊤) le_top
        simpa using this
      have hfker3 : ¬ 3 ∣ Nat.card f.ker := fun h3 => hK3 (h3.trans hfker_dvd_K)
      have hfker1 : Nat.card f.ker = 1 := by
        have hdvd3 : Nat.card f.ker ∣ 3 := by
          have := hfker_dvd_Z
          rwa [hZcard] at this
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd3 with h1 | h1
        · exact h1
        · rw [h1] at hfker3
          exact absurd dvd_rfl hfker3
      have hKmaptop : K.map (QuotientGroup.mk' (Subgroup.center T)) = ⊤ := by
        have h1 : (K ⊔ Subgroup.center T).map
            (QuotientGroup.mk' (Subgroup.center T)) = ⊤ := by
          rw [hKsup, Subgroup.map_top_of_surjective _
            (QuotientGroup.mk'_surjective (Subgroup.center T))]
        have h2 : (Subgroup.center T).map (QuotientGroup.mk' (Subgroup.center T)) = ⊥ := by
          rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        rwa [Subgroup.map_sup, h2, sup_bot_eq] at h1
      have hrange_top : f.range = ⊤ := by
        rw [show f = (QuotientGroup.mk' (Subgroup.center T)).comp K.subtype from rfl,
          MonoidHom.range_comp, Subgroup.range_subtype]
        exact hKmaptop
      have hcardK : Nat.card K = 360 := by
        have h := Subgroup.card_ker_mul_card_range f
        rw [hfker1, one_mul, hrange_top] at h
        rw [Subgroup.card_top, hQcard] at h
        omega
      rw [hcardK] at hK3
      norm_num at hK3
  have hMle : M.subgroupOf LB ≤ CFSG.pCore 2 ↥LB := by
    have h : M.subgroupOf LB ≤ π.ker :=
      (Subgroup.map_eq_bot_iff (H := M.subgroupOf LB) (f := π)).mp hKbot
    rwa [show π.ker = CFSG.pCore 2 ↥LB from QuotientGroup.ker_mk' _] at h
  intro x hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, hMle hx, rfl⟩

theorem J2Config.eq_lB_of_dvd (h : J2Config L d LB) {N : Subgroup G} (hNLB : N ≤ LB)
    (hN : LB ≤ Subgroup.normalizer (N : Set G)) (h27 : 27 ∣ Nat.card N ∨ 5 ∣ Nat.card N) :
    N = LB := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T := ↥LB ⧸ CFSG.pCore 2 ↥LB
  let π : ↥LB →* T := QuotientGroup.mk' _
  let M : Subgroup ↥LB := N.subgroupOf LB
  have hMnorm : M.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNLB).mpr hN
  let K : Subgroup T := M.map π
  have hKnorm : K.Normal := Subgroup.Normal.map hMnorm π (QuotientGroup.mk'_surjective _)
  have hKnotZ : ¬ K ≤ Subgroup.center T := by
    intro hKZ
    have hZcard := (tripleCover_card_data h.tripleCover).1
    have hKdvd3 : Nat.card K ∣ 3 := by
      have := Subgroup.card_dvd_of_le hKZ
      rwa [hZcard] at this
    have hcardM : Nat.card M = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNLB).toEquiv
    let f : M →* T := π.comp M.subtype
    have hfker2 : IsPGroup 2 f.ker := by
      change IsPGroup 2 ((π.comp M.subtype).ker)
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      exact IsPGroup.comap_subtype (H := CFSG.pCore 2 ↥LB) (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥LB) 2) (K := M)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := f.ker)).mp hfker2
    have hrangeK : f.range = K := by
      rw [show f = π.comp M.subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
    have hcardprod : 2 ^ k * Nat.card K = Nat.card N := by
      have := Subgroup.card_ker_mul_card_range f
      rw [hk, hrangeK, hcardM] at this
      exact this
    have hdvdK : 27 ∣ Nat.card K ∨ 5 ∣ Nat.card K := by
      rcases h27 with h27 | h5
      · left
        refine Nat.Coprime.dvd_of_dvd_mul_left (m := 2 ^ k) ?_ ?_
        · exact Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 27 2)
        · rw [hcardprod]
          exact h27
      · right
        refine Nat.Coprime.dvd_of_dvd_mul_left (m := 2 ^ k) ?_ ?_
        · exact Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 5 2)
        · rw [hcardprod]
          exact h5
    rcases hdvdK with hd | hd
    · exact absurd (hd.trans hKdvd3) (by norm_num)
    · exact absurd (hd.trans hKdvd3) (by norm_num)
  haveI : Group.IsPerfect ↥LB := h.isPerfect_lB
  have hperfT : Group.IsPerfect T :=
    Group.IsPerfect.ofSurjective (f := π) (QuotientGroup.mk'_surjective _)
  have hKtop : K = ⊤ := by
    rcases tripleCover_normal_le_center_or_sup_eq_top h.tripleCover hKnorm with hKZ | hKsup
    · exact absurd hKZ hKnotZ
    · exact tripleCover_eq_top_of_sup_center hperfT hKnorm hKsup
  have hsup : M ⊔ CFSG.pCore 2 ↥LB = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxK : π x ∈ K := by rw [hKtop]; exact Subgroup.mem_top _
    obtain ⟨m, hmM, hmx⟩ := Subgroup.mem_map.mp hxK
    have hker : m⁻¹ * x ∈ CFSG.pCore 2 ↥LB := by
      rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥LB)]
      change π (m⁻¹ * x) = 1
      rw [map_mul, map_inv, hmx, inv_mul_cancel]
    have hxeq : x = m * (m⁻¹ * x) := by group
    rw [hxeq]
    exact Subgroup.mul_mem_sup hmM hker
  let O : Subgroup ↥LB := CFSG.pCore 2 ↥LB
  let φ : O →* ↥LB ⧸ M := (QuotientGroup.mk' M).comp O.subtype
  have hφrange : φ.range = ⊤ := by
    have h1 : (M ⊔ O).map (QuotientGroup.mk' M) = ⊤ := by
      rw [show M ⊔ O = ⊤ from hsup,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective M)]
    have h2 : M.map (QuotientGroup.mk' M) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [Subgroup.map_sup, h2, bot_sup_eq] at h1
    rw [show φ = (QuotientGroup.mk' M).comp O.subtype from rfl,
      MonoidHom.range_comp, Subgroup.range_subtype]
    exact h1
  haveI : Group.IsNilpotent O :=
    IsPGroup.isNilpotent (p := 2) (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥LB) 2)
  have hOsolv : Group.IsSolvable O := IsNilpotent.to_isSolvable (G := O)
  haveI : Group.IsSolvable O := hOsolv
  have hφsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    exact hφrange
  have hQsolv : Group.IsSolvable (↥LB ⧸ M) :=
    Group.isSolvable_of_surjective (f := φ) hφsurj
  have hQperf : Group.IsPerfect (↥LB ⧸ M) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' M)
      (QuotientGroup.mk'_surjective M)
  haveI : Group.IsPerfect (↥LB ⧸ M) := hQperf
  have hQsingle : Subsingleton (↥LB ⧸ M) := by
    by_contra h
    haveI : Nontrivial (↥LB ⧸ M) := not_subsingleton_iff_nontrivial.mp h
    exact (Group.IsPerfect.not_isSolvable (G := ↥LB ⧸ M)) hQsolv
  have hMtop : M = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : QuotientGroup.mk' M x = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff (N := M) x).mp hx
  exact le_antisymm hNLB (Subgroup.subgroupOf_eq_top.mp hMtop)

theorem J2Config.exists_sylow (h : J2Config L d LB) :
    ∃ S : Subgroup G, S ≤ LB ∧ Nat.card S = 27 ∧ d ∈ S ∧
      ∀ s ∈ S, s ^ 3 ∈ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTcard := (tripleCover_card_data h.tripleCover).2.2
  have hLBcard : Nat.card ↥LB = Nat.card (CFSG.pCore 2 ↥LB) * 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥LB), hTcard,
      mul_comm]
  have h27LB : 27 ∣ Nat.card ↥LB := by
    rw [hLBcard]
    exact dvd_mul_of_dvd_right (by norm_num : 27 ∣ 1080) _
  have hHcard : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, h.orderOf_d]
  obtain ⟨S, hScard, hHS, hSL⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le (p := 3) (n := 3)
      (H := Subgroup.zpowers d) (L := LB) Nat.prime_three
      (by rw [hHcard]; norm_num) (by simpa using h27LB)
      (Subgroup.zpowers_le.mpr h.mem_lB)
  have hdS : d ∈ S := hHS (Subgroup.mem_zpowers d)
  let T := ↥LB ⧸ CFSG.pCore 2 ↥LB
  let π : ↥LB →* T := QuotientGroup.mk' _
  let Z : Subgroup T := Subgroup.center T
  let SL : Subgroup ↥LB := S.subgroupOf LB
  let S' : Subgroup T := SL.map π
  let dl : ↥LB := ⟨d, h.mem_lB⟩
  let dbar : T := π dl
  have hScard27 : Nat.card S = 27 := by
    rw [hScard]
    norm_num
  have hSLcard : Nat.card SL = 27 := by
    rw [← hScard27]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv
  have hSL3 : IsPGroup 3 SL := by
    refine IsPGroup.of_card (p := 3) (n := 3) ?_
    rw [hSLcard]
    norm_num
  have hdlord : orderOf dl = 3 := by
    change orderOf (⟨d, h.mem_lB⟩ : ↥LB) = 3
    rw [Subgroup.orderOf_mk, h.orderOf_d]
  have hdlO : dl ∉ CFSG.pCore 2 ↥LB := by
    intro hmem
    have h3dvd : 3 ∣ Nat.card (CFSG.pCore 2 ↥LB) := by
      rw [← hdlord]
      exact Subgroup.orderOf_dvd_natCard _ hmem
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := CFSG.pCore 2 ↥LB)).mp
      (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥LB) 2)
    rw [hk] at h3dvd
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
    norm_num at h32
  have hdbard : dbar ≠ 1 := by
    intro h1
    exact hdlO ((QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥LB) dl).mp h1)
  have hdbarord : orderOf dbar = 3 := by
    refine orderOf_eq_prime ?_ hdbard
    change (π dl) ^ 3 = 1
    rw [← map_pow, show dl ^ 3 = 1 by rw [← hdlord]; exact pow_orderOf_eq_one dl, map_one]
  have hdbar_center : dbar ∈ Z := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥LB) x
    change π x * π dl = π dl * π x
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (h.lB_le x.2).2))
  have hZeq : Subgroup.zpowers dbar = Z := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdbar_center) ?_
    rw [(tripleCover_card_data h.tripleCover).1, Nat.card_zpowers, hdbarord]
  have hfker2 : IsPGroup 2 (π.comp SL.subtype).ker := by
    change IsPGroup 2 ((π.comp SL.subtype).ker)
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact IsPGroup.comap_subtype (H := CFSG.pCore 2 ↥LB)
      (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥LB) 2) (K := SL)
  have hcardker : Nat.card (π.comp SL.subtype).ker = 1 := by
    obtain ⟨k, hk⟩ :=
      (IsPGroup.iff_card (p := 2) (G := (π.comp SL.subtype).ker)).mp hfker2
    have hdvd : Nat.card (π.comp SL.subtype).ker ∣ 27 := by
      have := Subgroup.card_dvd_of_le (H := (π.comp SL.subtype).ker) (K := ⊤) le_top
      simpa [hSLcard] using this
    rw [hk] at hdvd
    have hcop : Nat.Coprime (2 ^ k) 27 :=
      Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 27)
    have h1 : 2 ^ k = 1 := hcop.eq_one_of_dvd hdvd
    rw [hk, h1]
  have hS'card : Nat.card S' = 27 := by
    have h := Subgroup.card_ker_mul_card_range (π.comp SL.subtype)
    rw [hcardker, one_mul] at h
    have hrange : (π.comp SL.subtype).range = S' := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange, hSLcard] at h
    exact h
  have hdlSL : dl ∈ SL := by
    rw [Subgroup.mem_subgroupOf]
    exact hdS
  refine ⟨S, hSL, hScard27, hdS, ?_⟩
  intro s hs
  let sl : ↥LB := ⟨s, hSL hs⟩
  let sbar : T := π sl
  have hslSL : sl ∈ SL := by
    rw [Subgroup.mem_subgroupOf]
    exact hs
  have hsbar_mem : sbar ∈ S' := Subgroup.mem_map.mpr ⟨sl, hslSL, rfl⟩
  have hsbar_cube : sbar ^ 3 ∈ Z :=
    tripleCover_cube_mem_center h.tripleCover hS'card hsbar_mem
  have hcube_zpowers : sbar ^ 3 ∈ Subgroup.zpowers dbar := by
    rw [hZeq]
    exact hsbar_cube
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcube_zpowers
  let x : ↥LB := sl ^ 3 * (dl ^ k)⁻¹
  have hxSL : x ∈ SL :=
    SL.mul_mem (Subgroup.pow_mem SL hslSL 3) (SL.inv_mem (Subgroup.zpow_mem SL hdlSL k))
  have hxker : x ∈ CFSG.pCore 2 ↥LB := by
    rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥LB)]
    change π (sl ^ 3 * (dl ^ k)⁻¹) = 1
    rw [map_mul, map_pow, map_inv, map_zpow]
    change sbar ^ 3 * (dbar ^ k)⁻¹ = 1
    rw [← hk, mul_inv_cancel]
  have hdisj : Disjoint SL (CFSG.pCore 2 ↥LB) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) SL _ hSL3
      (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥LB) 2)
  have hxbot : x ∈ (⊥ : Subgroup ↥LB) := by
    rw [← hdisj.eq_bot]
    exact ⟨hxSL, hxker⟩
  have hx1 : x = 1 := Subgroup.mem_bot.mp hxbot
  have hpow : sl ^ 3 = dl ^ k := by
    have h := congrArg (fun z : ↥LB => z * dl ^ k) hx1
    simpa [x, mul_assoc] using h
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  change d ^ k = s ^ 3
  exact (congrArg (Subtype.val : ↥LB → G) hpow).symm

theorem J2Config.exists_mul_self_mem (h : J2Config L d LB) :
    ∃ t ∈ LB, t ∉ CFSG.Open.pCoreOf 2 LB ∧ t * t ∈ CFSG.Open.pCoreOf 2 LB := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T := ↥LB ⧸ CFSG.pCore 2 ↥LB
  let π : ↥LB →* T := QuotientGroup.mk' _
  obtain ⟨-, -, hTcard⟩ := tripleCover_card_data h.tripleCover
  have h2dvd : 2 ∣ Nat.card T := by rw [hTcard]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 h2dvd
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥LB) x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    norm_num at hx
  have htO : t ∉ CFSG.pCore 2 ↥LB := by
    intro htp
    apply hx1
    rw [← ht]
    exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥LB) t).mpr htp
  have ht2 : t * t ∈ CFSG.pCore 2 ↥LB := by
    rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥LB)]
    change QuotientGroup.mk' (CFSG.pCore 2 ↥LB) (t * t) = 1
    rw [map_mul, ht]
    exact (by simpa [pow_two, hx] using pow_orderOf_eq_one x : x * x = 1)
  have htdO : (t : G) ∉ CFSG.Open.pCoreOf 2 LB := by
    rintro ⟨y, hy, hyt⟩
    apply htO
    have : y = t := Subtype.ext (by simpa using hyt)
    rwa [this] at hy
  refine ⟨(t : G), t.2, htdO, ?_⟩
  exact Subgroup.mem_map.mpr ⟨t * t, ht2, rfl⟩

omit [Finite G] in
private theorem omegaZOf_eq_omegaG (Q : Subgroup G) :
    Sec3.omegaZOf Q = CFSG.RankThree.PartTwo.Sec3.omegaG Q := by
  unfold Sec3.omegaZOf
  rw [CFSG.RankThree.PartTwo.Sec3.map_omegaOneCenter, Subgroup.map_top,
    Subgroup.range_subtype]

omit [Finite G] in
theorem mem_omegaZOf_iff (Q : Subgroup G) {z : G} :
    z ∈ Sec3.omegaZOf Q ↔ z ∈ Q ∧ (∀ x ∈ Q, z * x = x * z) ∧ z * z = 1 := by
  rw [omegaZOf_eq_omegaG, CFSG.RankThree.PartTwo.Sec3.mem_omegaG]

theorem omegaZOf_pCoreOf_ne_bot {X : Subgroup G} (hX : CFSG.Open.pCoreOf 2 X ≠ ⊥) :
    Sec3.omegaZOf (CFSG.Open.pCoreOf 2 X) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 X with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hX
  have hZnt : Nontrivial (Subgroup.center Q) := hQ2.center_nontrivial
  have hC2 : IsPGroup 2 (Subgroup.center Q) := hQ2.to_subgroup (Subgroup.center Q)
  have hdvd : 2 ∣ Nat.card (Subgroup.center Q) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := Subgroup.center Q)).mp hC2
    have h1 : 1 < Nat.card (Subgroup.center Q) :=
      Finite.one_lt_card_iff_nontrivial.mpr hZnt
    rw [hk] at h1 ⊢
    exact dvd_pow_self 2 (by rintro rfl; simp at h1)
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 2 hdvd
  have hzord' : orderOf (z : Q) = 2 := by rwa [Subgroup.orderOf_coe]
  have hz2 : (z : Q) * (z : Q) = 1 := by
    rw [← pow_two, ← hzord']
    exact pow_orderOf_eq_one (z : Q)
  have hz2G : ((z : Q) : G) * ((z : Q) : G) = 1 := by
    have h := congrArg (Subtype.val : Q → G) hz2
    simpa using h
  have hzmem : ((z : Q) : G) ∈ CFSG.RankThree.PartTwo.Sec3.omegaG Q := by
    refine ⟨(z : Q).2, ?_, hz2G⟩
    intro x hx
    simpa using (congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨x, hx⟩)).symm
  have hz1' : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    norm_num at hzord
  have hz1 : ((z : Q) : G) ≠ 1 := by
    intro h
    have hq : (z : Q) = 1 := Subtype.ext h
    exact hz1' (Subtype.ext hq)
  rw [omegaZOf_eq_omegaG]
  intro hbot
  have : ((z : Q) : G) ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact hzmem
  exact hz1 (Subgroup.mem_bot.mp this)

omit [Finite G] in
theorem le_normalizer_omegaZOf_pCoreOf {X Y : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (X : Set G)) :
    Y ≤ Subgroup.normalizer (Sec3.omegaZOf (CFSG.Open.pCoreOf 2 X) : Set G) := by
  rw [omegaZOf_eq_omegaG]
  refine Subgroup.le_normalizer_iff.mpr ?_
  intro y hy z hz
  obtain ⟨hzQ, hzc, hz2⟩ :=
    (CFSG.RankThree.PartTwo.Sec3.mem_omegaG).mp hz
  have hyN : y ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X) (hY hy)
  refine (CFSG.RankThree.PartTwo.Sec3.mem_omegaG).mpr ⟨?_, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hyN z).mp hzQ
  · intro x hx
    have hx' : y⁻¹ * x * y ∈ CFSG.Open.pCoreOf 2 X := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)).inv_mem hyN) x).mp hx
      simpa using this
    have h := hzc _ hx'
    calc y * z * y⁻¹ * x = y * (z * (y⁻¹ * x * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * x * y) * z) * y⁻¹ := by rw [h]
      _ = x * (y * z * y⁻¹) := by group
  · calc y * z * y⁻¹ * (y * z * y⁻¹) = y * (z * z) * y⁻¹ := by group
      _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]

end CFSG.RankThree.PartTwo.J2Residue
