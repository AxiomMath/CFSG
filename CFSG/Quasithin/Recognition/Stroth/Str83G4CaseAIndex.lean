module


public import CFSG.Quasithin.Recognition.Stroth.BenderChief

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin

section General

variable {G : Type*} [Group G]

theorem caseA_relIndex_centralizer_le_card_of_comm_mem {B Z : Subgroup G} [Finite Z] {u : G}
    (hZB : ∀ z ∈ Z, ∀ b ∈ B, z * b = b * z) (hB : ∀ b ∈ B, b * u * b⁻¹ * u⁻¹ ∈ Z) :
    (B ⊓ Subgroup.centralizer ({u} : Set G)).relIndex B ≤ Nat.card Z := by
  classical
  have hmem : ∀ b ∈ B, u * (b : G) * u⁻¹ * (b : G)⁻¹ ∈ Z := by
    intro b hb
    have h := Z.inv_mem (hB b hb)
    convert h using 1
    group
  let f : B →* Z :=
    { toFun := fun b => ⟨u * (b : G) * u⁻¹ * (b : G)⁻¹, hmem b b.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        have hcent : (a : G) * (u * (b : G) * u⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ =
            u * (b : G) * u⁻¹ * (b : G)⁻¹ := by
          have h := hZB _ (hmem b b.2) (a : G) a.2
          rw [← h]
          group
        show u * ((a : G) * (b : G)) * u⁻¹ * ((a : G) * (b : G))⁻¹ =
          (u * (a : G) * u⁻¹ * (a : G)⁻¹) * (u * (b : G) * u⁻¹ * (b : G)⁻¹)
        calc u * ((a : G) * (b : G)) * u⁻¹ * ((a : G) * (b : G))⁻¹
            = (u * (a : G) * u⁻¹ * (a : G)⁻¹) *
                ((a : G) * (u * (b : G) * u⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
          _ = (u * (a : G) * u⁻¹ * (a : G)⁻¹) *
                (u * (b : G) * u⁻¹ * (b : G)⁻¹) := by rw [hcent] }
  have hker : f.ker = (B ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hb
      have h1 : u * (b : G) * u⁻¹ * (b : G)⁻¹ = 1 := by
        show ((f b : Z) : G) = ((1 : Z) : G)
        rw [hb]
      have h2 : u * (b : G) * u⁻¹ = (b : G) := by
        calc u * (b : G) * u⁻¹ = (u * (b : G) * u⁻¹ * (b : G)⁻¹) * (b : G) := by group
          _ = 1 * (b : G) := by rw [h1]
          _ = (b : G) := one_mul _
      have h3 : u * (b : G) = (b : G) * u := by
        calc u * (b : G) = (u * (b : G) * u⁻¹) * u := by group
          _ = (b : G) * u := by rw [h2]
      exact ⟨b.2, h3.symm⟩
    · rintro ⟨-, hc⟩
      apply Subtype.ext
      show u * (b : G) * u⁻¹ * (b : G)⁻¹ = 1
      rw [← hc]
      group
  calc (B ⊓ Subgroup.centralizer ({u} : Set G)).relIndex B
      = f.ker.index := by rw [Subgroup.relIndex, hker]
    _ = Nat.card f.range := Subgroup.index_ker f
    _ ≤ Nat.card Z :=
        Nat.card_le_card_of_injective (fun x : f.range => (x : Z)) Subtype.coe_injective

theorem caseA_relIndex_centralizerMod_section_le {Z L N X : Subgroup G} [Finite X] {u : G}
    (hZL : Z ≤ L) (hLN : L ≤ N) (hNX : N ≤ X) (hNZ : N ≤ Subgroup.normalizer (Z : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) (huZ : u ∈ Subgroup.normalizer (Z : Set G))
    (huL : u ∈ Subgroup.normalizer (L : Set G)) :
    (centralizerMod L N (Subgroup.zpowers u)).relIndex N ≤
      (centralizerMod Z X (Subgroup.zpowers u)).relIndex X := by
  set C := centralizerMod Z N (Subgroup.zpowers u) with hC
  set CL := centralizerMod L N (Subgroup.zpowers u) with hCL
  set A := centralizerMod Z X (Subgroup.zpowers u) with hA
  have hCeq : C = A ⊓ N := by
    ext x
    rw [mem_centralizerMod, Subgroup.mem_inf, mem_centralizerMod]
    constructor
    · intro hx
      exact ⟨⟨hNX hx.1, hx.2.1, hx.2.2⟩, hx.1⟩
    · rintro ⟨⟨hxX, hxZ, hxcomm⟩, hxN⟩
      exact ⟨hxN, hxZ, hxcomm⟩
  have hCCL : C ≤ CL := by
    intro x hx
    rw [mem_centralizerMod] at hx ⊢
    exact ⟨hx.1, hNL hx.1, fun v hv => hZL (hx.2.2 v hv)⟩
  haveI : Finite ↥N :=
    Finite.of_injective (Subgroup.inclusion hNX) (Subgroup.inclusion_injective hNX)
  have hle : CL.relIndex N ≤ C.relIndex N :=
    Subgroup.relIndex_le_of_le_left hCCL Subgroup.index_ne_zero_of_finite
  have hAN : A.relIndex N ≤ A.relIndex X :=
    Subgroup.relIndex_le_of_le_right hNX Subgroup.index_ne_zero_of_finite
  calc CL.relIndex N ≤ C.relIndex N := hle
    _ = (A ⊓ N).relIndex N := by rw [hCeq]
    _ = A.relIndex N := Subgroup.inf_relIndex_right A N
    _ ≤ A.relIndex X := hAN

theorem caseA_relIndex_centralizerMod_le_relIndex_centralizer {Z N : Subgroup G} [Finite N]
    {u : G} (hNZ : N ≤ Subgroup.normalizer (Z : Set G)) :
    (centralizerMod Z N (Subgroup.zpowers u)).relIndex N ≤
      (N ⊓ Subgroup.centralizer ({u} : Set G)).relIndex N := by
  apply Subgroup.relIndex_le_of_le_left ?_ Subgroup.index_ne_zero_of_finite
  intro x hx
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hx
  rw [mem_centralizerMod]
  refine ⟨hx.1, hNZ hx.1, fun v hv => ?_⟩
  have hcomm : x * v = v * x := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_right (show Commute x u from hx.2) k).eq
  rw [hcomm]
  simp

end General

section Finite

variable {G : Type} [Group G] [Finite G]

theorem caseA_exists_chiefStep_of_not_le_centralizerMod {H U X N : Subgroup G}
    (hU : IsPGroup 2 U) (hUH : U ≤ H) (hUQ : U ≤ pCoreOf 2 H) (hXU : IsNormalIn H U X)
    (hNU : IsNormalIn H U N) (hXN : X ≤ N)
    (hnot : ¬ twoResidual H ≤ centralizerMod X H N) :
    ∃ L K : Subgroup G, IsChiefStep H U L K ∧ X ≤ L ∧ K ≤ N ∧
      ¬ twoResidual H ≤ centralizerMod L H K := by
  by_contra hcon
  have hcon' : ∀ L K : Subgroup G, IsChiefStep H U L K → X ≤ L → K ≤ N →
      twoResidual H ≤ centralizerMod L H K := by
    intro L K hstep hXL hKN
    by_contra hnc
    exact hcon ⟨L, K, hstep, hXL, hKN, hnc⟩
  obtain ⟨T, hT, hQT⟩ :=
    F1.exists_isSylowTwoOf_ge (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  obtain ⟨c, hser⟩ := F112W.exists_isChiefSeriesBetween hXU N hNU hXN
  have key : ∀ (M : Subgroup G) (m : ℕ), F112W.IsChiefSeriesBetween H U X M m → M ≤ N →
      m = 0 := by
    intro M m hserM hMN
    induction hserM with
    | refl => rfl
    | @central P L n hstep hcent hs ih =>
        exact ih (hstep.2.2.1.le.trans hMN)
    | @noncentral P L n hstep hnc hs ih =>
        exfalso
        apply hnc
        have hP : ⁅P, oTwoUpper H⁆ ≤ L := by
          rw [Subgroup.commutator_le]
          intro k hk t ht
          have ht' : t ∈ twoResidual H := by
            rw [F6.twoResidual_eq_oTwoUpper]
            exact ht
          have hcent := hcon' L P hstep hs.le hMN ht'
          have h1 : t * k * t⁻¹ * k⁻¹ ∈ L := hcent.2.2 k hk
          have h2 : (t * k * t⁻¹ * k⁻¹)⁻¹ ∈ L := L.inv_mem h1
          have e : (t * k * t⁻¹ * k⁻¹)⁻¹ = k * t * k⁻¹ * t⁻¹ := by group
          rwa [e] at h2
        exact D15Proof.isCentralStep_of_commutator_le hT hUH
          (hstep.1.1.trans (hUQ.trans (F7.isSylowTwoOf_pCoreOf_le hT))) hstep hP
  have hn : c = 0 := key N c hser le_rfl
  rw [hn] at hser
  have hcommX : ⁅N, oTwoUpper H⁆ ≤ X :=
    (F112W.isChiefSeriesBetween_zero_iff hUH hUQ hXU hNU hXN).mp hser
  apply hnot
  rw [F6.twoResidual_eq_oTwoUpper]
  intro t ht
  have htH : t ∈ H := oTwoUpper_le H ht
  refine ⟨htH, D14.le_normalizer_of_isNormalIn hXU htH, fun k hk => ?_⟩
  have h1 : k * t * k⁻¹ * t⁻¹ ∈ X := (Subgroup.commutator_le.mp hcommX) k hk t ht
  have h2 : (k * t * k⁻¹ * t⁻¹)⁻¹ ∈ X := X.inv_mem h1
  have e : (k * t * k⁻¹ * t⁻¹)⁻¹ = t * k * t⁻¹ * k⁻¹ := by group
  rwa [e] at h2

theorem caseA_not_isCentralStep_of_not_le_centralizerMod {H L K : Subgroup G}
    (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hnot : ¬ twoResidual H ≤ centralizerMod L H K) : ¬ IsCentralStep H L K := by
  intro hcent
  apply hnot
  intro t ht
  rw [F6.twoResidual_eq_oTwoUpper] at ht
  have htH : t ∈ H := oTwoUpper_le H ht
  have hcomm : ⁅oTwoUpper H, K⁆ ≤ L := D14.commutator_le_of_isCentralStep hcent
  exact ⟨htH, hHL htH, fun k hk => (Subgroup.commutator_le.mp hcomm) t ht k hk⟩

theorem caseA_sq_le_relIndex_centralizerMod_section
    {H U Z X : Subgroup G} {q : ℕ} (hH : IsSzU3Quot (oTwoQuot ↥H) q) (hU : IsPGroup 2 U)
    (hUH : U ≤ H) (hUQ : U ≤ pCoreOf 2 H) (hZU : IsNormalIn H U Z) (hXU : IsNormalIn H U X)
    (hZX : Z ≤ X) (hnot : ¬ twoResidual H ≤ centralizerMod Z H X) {t : G} (htH : t ∈ H)
    (ht : t * t ∈ pCoreOf 2 H) (htO : t ∉ pCoreOf 2 H) :
    q ^ 2 ≤ (centralizerMod Z X (Subgroup.zpowers t)).relIndex X := by
  obtain ⟨L, K, hstep, hZL, hKX, hnc⟩ :=
    caseA_exists_chiefStep_of_not_le_centralizerMod hU hUH hUQ hZU hXU hZX hnot
  have hnc' : ¬ IsCentralStep H L K :=
    caseA_not_isCentralStep_of_not_le_centralizerMod
      (D14.le_normalizer_of_isNormalIn hstep.2.1) hnc
  have hM7 : q ^ 2 ≤ (centralizerMod L K (Subgroup.zpowers t)).relIndex K :=
    sq_le_relIndex_centralizerMod hH hU hUH hstep hnc' htH ht htO
  refine hM7.trans ?_
  have hKL : L ≤ K := hstep.2.2.1.le
  have hKH : K ≤ H := hstep.1.1.trans hUH
  have hKZ : K ≤ Subgroup.normalizer (Z : Set G) :=
    hKH.trans (D14.le_normalizer_of_isNormalIn hZU)
  have hKNL : K ≤ Subgroup.normalizer (L : Set G) :=
    hKH.trans (D14.le_normalizer_of_isNormalIn hstep.2.1)
  have htZ : t ∈ Subgroup.normalizer (Z : Set G) :=
    (D14.le_normalizer_of_isNormalIn hZU) htH
  have htL : t ∈ Subgroup.normalizer (L : Set G) :=
    (D14.le_normalizer_of_isNormalIn hstep.2.1) htH
  exact caseA_relIndex_centralizerMod_section_le hZL hKL hKX hKZ hKNL htZ htL

end Finite

end CFSG.Quasithin.Stroth

end
