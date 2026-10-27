module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523Sz
public import CFSG.RankThree.PartTwo.Sec13.Item136Transfer
public import CFSG.Quasithin.Background.SmithD39TwoSQTK
public import CFSG.Quasithin.Background.A3Structure36AList
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs

public section

namespace CFSG.Quasithin.SmithD39Two

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin

section Cores

variable {G : Type} [Group G]

theorem le_normalizer_inf_centralizer {M N : Subgroup G}
    (hNM : M ≤ Subgroup.normalizer (N : Set G)) :
    M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (N : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro m hm c hc
  obtain ⟨hcM, hcN⟩ := Subgroup.mem_inf.mp hc
  refine Subgroup.mem_inf.mpr ⟨M.mul_mem (M.mul_mem hm hcM) (M.inv_mem hm), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hn' : m⁻¹ * n * m ∈ N := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hNM (M.inv_mem hm)) n).mp hn
    rwa [inv_inv] at h1
  have h1 := Subgroup.mem_centralizer_iff.mp hcN _ hn'
  calc n * (m * c * m⁻¹) = m * ((m⁻¹ * n * m) * c) * m⁻¹ := by group
    _ = m * (c * (m⁻¹ * n * m)) * m⁻¹ := by rw [h1]
    _ = m * c * m⁻¹ * n := by group

variable [Finite G]

theorem pCoreOf_le_pCoreOf_of_le_normalizer (p : ℕ) [Fact p.Prime] {C M : Subgroup G}
    (hCM : C ≤ M) (hMC : M ≤ Subgroup.normalizer (C : Set G)) : pCoreOf p C ≤ pCoreOf p M :=
  le_pCoreOf_of_le_normalizer p ((pCoreOf_le p C).trans hCM)
    (hMC.trans (normalizer_le_normalizer_pCoreOf p C)) (pCoreOf_isPGroup p C)

end Cores

section Bender

variable {G : Type} [Group G] [Finite G]

theorem exists_moved_piece {M N E : Subgroup G}
    (hO2 : pCoreOf 2 (M ⊓ Subgroup.centralizer (N : Set G)) = ⊥)
    (hEC : E ≤ M ⊓ Subgroup.centralizer (N : Set G)) (hE2 : IsPGroup 2 ↥E) (hE1 : E ≠ ⊥)
    (hNM : M ≤ Subgroup.normalizer (N : Set G)) :
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
        ¬ pCoreOf p (M ⊓ Subgroup.centralizer (N : Set G)) ≤ Subgroup.centralizer (E : Set G)) ∨
      ∃ K : Subgroup G, K ∈ cComp M ∧ CFSG.IsQuasisimple ↥K ∧
        K ≤ M ⊓ Subgroup.centralizer (N : Set G) ∧ ¬ E ≤ Subgroup.centralizer (K : Set G) := by
  classical
  set C : Subgroup G := M ⊓ Subgroup.centralizer (N : Set G) with hCdef
  by_cases hF : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ pCoreOf p C ≤ Subgroup.centralizer (E : Set G)
  · exact Or.inl hF
  right
  push Not at hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E' := E.subgroupOf C with hE'
  have hE'2 : IsPGroup 2 ↥E' := hE2.of_equiv (Subgroup.subgroupOfEquivOfLe hEC).symm
  have hE'ne : E' ≠ ⊥ := by
    intro hb
    apply hE1
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hEC ha⟩ : ↥C) ∈ E' := ha
    rw [hb, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  have hO2C : CFSG.pCore 2 ↥C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxC : (x : G) ∈ pCoreOf 2 C := ⟨x, by assumption, rfl⟩
    rw [hO2, Subgroup.mem_bot] at hxC
    rw [Subgroup.mem_bot]
    exact Subtype.ext hxC
  have hF' : ∀ p : (Nat.card ↥C).primeFactors, CFSG.pCore (p : ℕ) ↥C ≤
      Subgroup.centralizer (E' : Set ↥C) := by
    intro p x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hxC : (x : G) ∈ pCoreOf (p : ℕ) C := ⟨x, by assumption, rfl⟩
    by_cases hp2 : (p : ℕ) = 2
    · rw [hp2, hO2, Subgroup.mem_bot] at hxC
      have hx1 : x = 1 := Subtype.ext hxC
      rw [hx1, mul_one, one_mul]
    · have hc := Subgroup.mem_centralizer_iff.mp
        (hF p (Nat.prime_of_mem_primeFactors p.2) hp2 hxC) a (Subgroup.mem_subgroupOf.mp ha)
      exact Subtype.ext hc
  obtain ⟨K', hK', hK'E⟩ := H13.exists_isComponentOf_not_le_centralizer hE'2 hO2C hE'ne hF'
  obtain ⟨-, hKsub, hKq⟩ := hK'
  set K := K'.map C.subtype with hKdef
  have hKC : K ≤ C := Subgroup.map_subtype_le K'
  have hKq' : CFSG.IsQuasisimple ↥K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (K'.equivMapOfInjective C.subtype C.subtype_injective) (H13.isQuasisimple_of_gw hKq)
  have hKsub' : K'.IsSubnormal :=
    Subgroup.IsSubnormal.trans le_top hKsub Subgroup.IsSubnormal.top
  have hKsubC : CFSG.Open.IsSubnormal K C := by
    rw [CFSG.Quasithin.isSubnormal_iff_subgroupOf hKC, hKdef]
    show ((K'.map C.subtype).comap C.subtype).IsSubnormal
    rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    exact hKsub'
  have hCsub : CFSG.Open.IsSubnormal C M :=
    A3.subnormal_of_normal inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
        (le_normalizer_inf_centralizer hNM))
  refine ⟨K, H13.mem_cComp_of_isQuasisimple_of_isSubnormal hKq'
    (A3.subnormal_trans hKsubC hCsub), hKq', hKC, fun hEK => hK'E ?_⟩
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h1 := Subgroup.mem_centralizer_iff.mp (hEK (Subgroup.mem_subgroupOf.mp ha)) _
    ⟨e, he, rfl⟩
  exact Subtype.ext h1

end Bender

section Burnside

theorem conj_pow_odd_eq_inv {X : Type*} [Group X] {g y : X} (hgy : g * y * g⁻¹ = y⁻¹) {b : ℕ}
    (hb : Odd b) : g ^ b * y * (g ^ b)⁻¹ = y⁻¹ := by
  have hinv : g * y⁻¹ * g⁻¹ = y := by
    have h1 : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [h1, hgy, inv_inv]
  have hg2 : Commute (g * g) y := by
    have h1 : (g * g) * y * (g * g)⁻¹ = y := by
      have h2 : (g * g) * y * (g * g)⁻¹ = g * (g * y * g⁻¹) * g⁻¹ := by group
      rw [h2, hgy, hinv]
    show (g * g) * y = y * (g * g)
    calc (g * g) * y = (g * g) * y * (g * g)⁻¹ * (g * g) := by group
      _ = y * (g * g) := by rw [h1]
  obtain ⟨c, rfl⟩ := hb
  have hc : Commute ((g * g) ^ c) y⁻¹ := (hg2.pow_left c).inv_right
  have h3 : g ^ (2 * c + 1) * y * (g ^ (2 * c + 1))⁻¹ =
      (g * g) ^ c * (g * y * g⁻¹) * ((g * g) ^ c)⁻¹ := by
    rw [pow_succ, pow_mul, pow_two]
    group
  rw [h3, hgy, hc.eq, mul_inv_cancel_right]

theorem exists_two_elt_inverting {G : Type*} [Group G] [Finite G] (hK : CFSG.IsQuasisimple G)
    (h3 : 3 ∣ Nat.card (G ⧸ Subgroup.center G)) (hcyc : ∀ P : Sylow 3 G, IsCyclic ↥P) :
    ∃ y x : G, orderOf y = 3 ∧ y ∉ Subgroup.center G ∧ (∃ k : ℕ, x ^ 2 ^ k = 1) ∧
      x * y * x⁻¹ = y⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 G) := inferInstance
  have h3G : 3 ∣ Nat.card G := h3.trans (Subgroup.card_quotient_dvd_card _)
  have hP1 : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card h3G
  have hPc : IsCyclic ↥P := hcyc P
  have hcomm : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x :=
    fun x hx y hy => RankThree.PartTwo.Sec13.mul_comm_of_isCyclic hx hy
  have hNC : ¬ Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
    intro hNC
    have hcompl := MonoidHom.ker_transferSylow_isComplement' P hNC
    have hker : (MonoidHom.transferSylow P hNC).ker = ⊤ := by
      rw [eq_top_iff, ← hK.1.commutator_eq_top, _root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      simp only [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_inv]
      have hab : MonoidHom.transferSylow P hNC a * MonoidHom.transferSylow P hNC b =
          MonoidHom.transferSylow P hNC b * MonoidHom.transferSylow P hNC a :=
        Subtype.ext (hcomm _ (MonoidHom.transferSylow P hNC a).2 _
          (MonoidHom.transferSylow P hNC b).2)
      rw [hab]
      group
    rw [hker] at hcompl
    have hcard := hcompl.card_mul_card
    rw [Subgroup.card_top] at hcard
    have hP1' : Nat.card (P : Subgroup G) = 1 := by
      have hpos : 0 < Nat.card G := Nat.card_pos
      nlinarith
    exact hP1 (Subgroup.eq_bot_of_card_eq _ hP1')
  obtain ⟨g, hgN, hgC⟩ := Set.not_subset.mp hNC
  set n := (P : Subgroup G).relIndex (Subgroup.normalizer (P : Set G)) with hn
  have hn3 : ¬ 3 ∣ n := fun hd => P.not_dvd_index (hd.trans
    (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))
  have hgn : g ^ n ∈ (P : Subgroup G) := by
    have : ((P : Subgroup G).subgroupOf (Subgroup.normalizer (P : Set G))).Normal :=
      Subgroup.normal_in_normalizer
    have h1 := Subgroup.pow_index_mem
      ((P : Subgroup G).subgroupOf (Subgroup.normalizer (P : Set G)))
      (⟨g, hgN⟩ : ↥(Subgroup.normalizer (P : Set G)))
    rw [Subgroup.mem_subgroupOf] at h1
    exact h1
  have hfix : ¬ ∀ x ∈ (P : Subgroup G), x ^ 3 = 1 → g * x * g⁻¹ = x := by
    intro hfix
    apply hgC
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    have key := RankThree.PartTwo.Sec13.conj_eq_of_coprime_pow P.isPGroup' hcomm hgN hn3
      (fun y hy => by rw [hcomm _ hgn y hy, mul_inv_cancel_right]) hfix hx
    calc x * g = g * x * g⁻¹ * g := by rw [key]
      _ = g * x := by group
  push Not at hfix
  obtain ⟨y, hyP, hy3, hgy⟩ := hfix
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hgy (by group)
  have hgyP : g * y * g⁻¹ ∈ (P : Subgroup G) := (Subgroup.mem_normalizer_iff.mp hgN y).mp hyP
  have hgy3 : (g * y * g⁻¹) ^ 3 = 1 := by
    rw [← MulAut.conj_apply, ← map_pow, hy3, map_one]
  have hinv : g * y * g⁻¹ = y⁻¹ := by
    by_contra hne
    refine S1417.not_isCyclic_of_four_cubes (C := ↥P) (α := ⟨y, hyP⟩)
      (β := ⟨g * y * g⁻¹, hgyP⟩) (Subtype.ext hy3) (Subtype.ext hgy3) ?_ ?_ ?_ ?_ hPc
    · intro h
      exact hy1 (congrArg Subtype.val h)
    · intro h
      apply hy1
      have h1 : g * y * g⁻¹ = 1 := congrArg Subtype.val h
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · intro h
      exact hgy (congrArg Subtype.val h)
    · intro h
      exact hne (congrArg Subtype.val h)
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨y, g ^ b, orderOf_eq_prime hy3 hy1, ?_, ⟨a, ?_⟩, conj_pow_odd_eq_inv hinv hb⟩
  · intro hyZ
    apply hy1
    refine eq_one_of_eq_inv_of_pow_three hy3 ?_
    rw [← conj_pow_odd_eq_inv hinv hb, Subgroup.mem_center_iff.mp hyZ (g ^ b),
      mul_inv_cancel_right]
  · rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]

end Burnside

section Suzuki

variable {G : Type} [Group G] [Finite G]

theorem suzukiModel_of_le {M K : Subgroup G} (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) (hMq : IsQuotientOfSQTKTC ↥M) (hKM : K ≤ M)
    (hKq : CFSG.IsQuasisimple ↥K) (h3 : ¬ 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)) :
    ∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ Subgroup.center ↥K) 2 n := by
  obtain ⟨S, _, _, hSQT, hKS, φ, hφ⟩ := hMq
  have hSQ : SQTKGroup S := ⟨fun p hp hp2 => hSQT p hp hp2, hKS⟩
  set Hs : Subgroup S := (K.subgroupOf M).comap φ with hHs
  let ψ : ↥Hs →* ↥K := (Subgroup.subgroupOfEquivOfLe hKM).toMonoidHom.comp
    (φ.subgroupComap (K.subgroupOf M))
  have hψ : Function.Surjective ψ := by
    intro g
    obtain ⟨h, hh⟩ := hφ ⟨(g : G), hKM g.2⟩
    have hmem : h ∈ Hs := by
      rw [hHs, Subgroup.mem_comap, hh]
      exact g.2
    refine ⟨⟨h, hmem⟩, Subtype.ext ?_⟩
    show ((φ h : ↥M) : G) = g
    rw [hh]
  let π : ↥Hs →* ↥K ⧸ Subgroup.center ↥K := (QuotientGroup.mk' _).comp ψ
  have hπs : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp hψ
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπs
  have hsimple : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKq.2.1
  have hsimple' : IsSimpleGroup (↥Hs ⧸ π.ker) := MulEquiv.isSimpleGroup e
  have hnab : ∃ a b : ↥Hs ⧸ π.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKq.2.2
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hlist : A23List (↥K ⧸ Subgroup.center ↥K) :=
    A36A.a23List_of_mulEquiv e.symm (hA23 _ hSQ Hs π.ker hsimple' hnab)
  exact hSzF _ hsimple hlist h3

theorem suzukiModel_of_le_of_not_dvd {M K : Subgroup G} (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) (hMq : IsQuotientOfSQTKTC ↥M) (hKM : K ≤ M)
    (hKq : CFSG.IsQuasisimple ↥K) (h3 : ¬ 3 ∣ Nat.card ↥K) :
    ∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ Subgroup.center ↥K) 2 n :=
  suzukiModel_of_le hA23 hSzF hMq hKM hKq fun h => h3 (h.trans
    (Subgroup.card_quotient_dvd_card _))

end Suzuki

end CFSG.Quasithin.SmithD39Two
