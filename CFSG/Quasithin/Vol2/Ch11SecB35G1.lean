module

public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLiftLie
public import CFSG.Quasithin.Background.E6TorusCover
public import CFSG.Quasithin.H13.KGFact22TorusFacts
public import CFSG.Quasithin.Vol2.KGNatSL2
public import CFSG.Quasithin.Vol2.Ch11SecBRootLiftE22

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

section Images

variable {U : Subgroup G} (hU : IsElemAbelian 2 U)

omit [Finite G] in
theorem card_autI_eq_relIndex {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card ↥(autI hU K) = (K ⊓ Subgroup.centralizer (U : Set G)).relIndex K := by
  rw [autI_eq_autOn]
  exact card_autOn_eq_relIndex hK

theorem isSylowIn_autI_of {S X : Subgroup G} (hS : QuasithinUnique.IsSylowTwoOf S X)
    (hX : X ≤ Subgroup.normalizer (U : Set G)) : IsSylowIn 2 (autI hU S) (autI hU X) := by
  have hSX := hS.1
  set C := Subgroup.centralizer (U : Set G) with hCdef
  refine ⟨autI_mono hU hSX, E3.isPGroup_autI hU (hSX.trans hX) hS.2.1, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (autI hU S) (autI hU X)
  rw [inf_eq_left.2 (autI_mono hU hSX), card_autI_eq_relIndex hU hX,
    card_autI_eq_relIndex hU (hSX.trans hX)] at h1
  have e1 := Subgroup.relIndex_mul_relIndex (S ⊓ C) (X ⊓ C) X (inf_le_inf_right _ hSX)
    inf_le_left
  have e2 := Subgroup.relIndex_mul_relIndex (S ⊓ C) S X inf_le_left hSX
  have h2 : (X ⊓ C).relIndex X * (S ⊓ C).relIndex (X ⊓ C) =
      (S ⊓ C).relIndex S * S.relIndex X := by
    rw [mul_comm, e1, e2]
  have hdvd : (autI hU S).relIndex (autI hU X) ∣ S.relIndex X := by
    refine ⟨(S ⊓ C).relIndex (X ⊓ C), ?_⟩
    have hpos : 0 < (S ⊓ C).relIndex S := Nat.pos_of_ne_zero (E3.relIndex_ne_zero' _ _)
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc (S ⊓ C).relIndex S * S.relIndex X = (X ⊓ C).relIndex X * (S ⊓ C).relIndex (X ⊓ C) :=
          h2.symm
      _ = (autI hU S).relIndex (autI hU X) * (S ⊓ C).relIndex S * (S ⊓ C).relIndex (X ⊓ C) := by
          rw [h1]
      _ = (S ⊓ C).relIndex S *
          ((autI hU S).relIndex (autI hU X) * (S ⊓ C).relIndex (X ⊓ C)) := by ring
  exact fun h => hS.2.2 (h.trans hdvd)

omit [Finite G] in
theorem autI_mul_comm_of {B S : Subgroup G} (hB : B ≤ Subgroup.normalizer (U : Set G))
    (hS : S ≤ Subgroup.normalizer (U : Set G))
    (hBS : (B : Set G) * (S : Set G) = (S : Set G) * (B : Set G)) :
    (autI hU B : Set (MulAut (IntMod U hU))) * (autI hU S : Set _) =
      (autI hU S : Set _) * (autI hU B : Set _) := by
  set N := Subgroup.normalizer (U : Set G)
  have himg : ∀ X : Subgroup G, X ≤ N →
      ((X.subgroupOf N : Subgroup ↥N) : Set ↥N).image N.subtype = (X : Set G) := by
    intro X hX
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hX hx⟩, hx, rfl⟩
  have hBS' : ((B.subgroupOf N : Subgroup ↥N) : Set ↥N) * (S.subgroupOf N : Subgroup ↥N) =
      ((S.subgroupOf N : Subgroup ↥N) : Set ↥N) * (B.subgroupOf N : Subgroup ↥N) := by
    apply Set.image_injective.2 N.subtype_injective
    rw [Set.image_mul, Set.image_mul, himg B hB, himg S hS, hBS]
  have e : ∀ X : Subgroup G, (autI hU X : Set (MulAut (IntMod U hU))) =
      (convI hU) '' ((X.subgroupOf N : Subgroup ↥N) : Set ↥N) := fun X => by
    rw [autI, Subgroup.coe_map]
  rw [e B, e S, ← Set.image_mul, ← Set.image_mul, hBS']

omit [Finite G] in
theorem autI_cyclic_of {Y : Subgroup G} (hY : Y ≤ Subgroup.normalizer (U : Set G))
    (hYU : Y ⊓ Subgroup.centralizer (U : Set G) = ⊥) (hYc : IsCyclic ↥Y) :
    IsCyclic ↥(autI hU Y) ∧ Nat.card ↥(autI hU Y) = Nat.card Y := by
  refine ⟨?_, by rw [card_autI_eq_relIndex hU hY, hYU, Subgroup.relIndex_bot_left]⟩
  set N := Subgroup.normalizer (U : Set G)
  have hYc' : IsCyclic ↥(Y.subgroupOf N) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hY).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hY).symm.surjective
  let φ : ↥(Y.subgroupOf N) →* ↥(autI hU Y) :=
    ((convI hU).comp (Y.subgroupOf N).subtype).codRestrict (autI hU Y)
      (fun y => Subgroup.mem_map_of_mem _ y.2)
  refine isCyclic_of_surjective φ ?_
  rintro ⟨ψ, ⟨y, hy, rfl⟩⟩
  exact ⟨⟨y, hy⟩, rfl⟩

theorem le_nPrime_autI {B T Y : Subgroup G} (hBN : B ≤ Subgroup.normalizer (U : Set G))
    (hTN : T ≤ Subgroup.normalizer (U : Set G))
    (hBU : B ⊓ Subgroup.centralizer (U : Set G) = ⊥)
    (hTS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (U : Set G)))
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBodd : Odd (Nat.card B))
    (hBT : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) (hYB : Y ≤ B)
    (hYc : IsCyclic ↥Y) {c : ℕ} (hYcard : Nat.card Y = 2 ^ c - 1) :
    c ≤ E3.nPrime (autI hU ⊤) := by
  have hYU : Y ⊓ Subgroup.centralizer (U : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hYB).trans hBU.le)
  obtain ⟨hYc', hYcard'⟩ := autI_cyclic_of hU (hYB.trans hBN) hYU hYc
  have htop : autI hU (Subgroup.normalizer (U : Set G)) = autI hU ⊤ := by
    simp only [autI, Subgroup.subgroupOf_self, Subgroup.top_subgroupOf]
  refine E3.le_nPrime (Y := autI hU Y) (B := autI hU B) (S := autI hU T) (c := c)
    (autI_mono hU hYB) (autI_mono hU le_top) hYc' (hYcard'.trans hYcard) ?_ ?_ ?_
    (autI_mul_comm_of hU hBN hTN hBT)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBab _ hx _ hy)
  · have h1 := Subgroup.card_map_dvd (B.subgroupOf (Subgroup.normalizer (U : Set G))) (convI hU)
    have h2 : Nat.card ↥(B.subgroupOf (Subgroup.normalizer (U : Set G))) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
    rw [h2] at h1
    exact Odd.of_dvd_nat hBodd h1
  · rw [← htop]
    exact isSylowIn_autI_of hU hTS le_rfl

end Images

theorem exists_cyclic_le_hall {H T MH K B : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hmin : MinParabolic H T MH) (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hlie : E2.E22LieCases H T MH K) (hF : Nat.card F = 2 ^ k) (hk : 2 ≤ k)
    (hiso : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B MH) :
    ∃ Y : Subgroup G, Y ≤ B ∧ IsCyclic ↥Y ∧ Nat.card Y = 2 ^ k - 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := k) (by rw [← Nat.card_eq_fintype_card, hF])
  have h4F : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨-, -, hsolv, -⟩ :=
    E2.e22BorelLift_lie (E2.e22TorusCover_of_facts H13.e22TorusFacts_holds) hmin hKc hHK hlie
  obtain ⟨-, -, -, S, hS, hMK⟩ := hlie.exists_borel
  obtain ⟨eK⟩ := hiso
  obtain ⟨⟨eKs⟩, -⟩ := E1.RootLift.star_facts (A := ⊥) h4F hmin hKc eK bot_le
  set Ks := E2.star MH H K with hKs
  set U : Subgroup SL(2, F) := (S.subgroupOf Ks).map eKs.toMonoidHom with hU
  have hU2 : IsPGroup 2 ↥U := hS.2.1.comap_subtype.map _
  have hUidx : ¬ 2 ∣ U.index := by
    rw [hU, Subgroup.index_map_of_bijective eKs.bijective]
    exact hS.2.2
  obtain ⟨g, hg⟩ := KGNat.exists_conj_utri_eq_of_index hU2 hUidx
  obtain ⟨-, d, hd, hdo⟩ := KGNat.normalizer_conj_utri (F := F) g
  rw [hg] at hd
  set d' : ↥Ks := eKs.symm d with hd'
  have key : ∀ z : ↥Ks, z ∈ S.subgroupOf Ks ↔ eKs z ∈ U := fun z => by
    rw [hU, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hd'S : (d' : E2.StarQuot MH H) ∈ Subgroup.normalizer (S : Set (E2.StarQuot MH H)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    by_cases hy : y ∈ Ks
    · have e1 : eKs (d' * ⟨y, hy⟩ * d'⁻¹) = d * eKs ⟨y, hy⟩ * d⁻¹ := by
        rw [map_mul, map_mul, map_inv, hd', MulEquiv.apply_symm_apply]
      calc y ∈ S ↔ (⟨y, hy⟩ : ↥Ks) ∈ S.subgroupOf Ks := Iff.rfl
        _ ↔ eKs ⟨y, hy⟩ ∈ U := key _
        _ ↔ d * eKs ⟨y, hy⟩ * d⁻¹ ∈ U := Subgroup.mem_normalizer_iff.mp hd _
        _ ↔ eKs (d' * ⟨y, hy⟩ * d'⁻¹) ∈ U := by rw [e1]
        _ ↔ (d' * ⟨y, hy⟩ * d'⁻¹ : ↥Ks) ∈ S.subgroupOf Ks := (key _).symm
        _ ↔ (d' : E2.StarQuot MH H) * y * (d' : E2.StarQuot MH H)⁻¹ ∈ S := Iff.rfl
    · have h1 : y ∉ S := fun h => hy (hS.1 h)
      have h2 : (d' : E2.StarQuot MH H) * y * (d' : E2.StarQuot MH H)⁻¹ ∉ S := by
        intro h
        apply hy
        have h3 : (d' : E2.StarQuot MH H)⁻¹ * ((d' : E2.StarQuot MH H) * y *
            (d' : E2.StarQuot MH H)⁻¹) * (d' : E2.StarQuot MH H) ∈ Ks :=
          Ks.mul_mem (Ks.mul_mem (Ks.inv_mem d'.2) (hS.1 h)) d'.2
        simpa [mul_assoc] using h3
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  have hd'M : (d' : E2.StarQuot MH H) ∈ E2.star MH H (MH ⊓ K) := by
    rw [hMK]
    exact ⟨d'.2, hd'S⟩
  have hd'o : orderOf (d' : E2.StarQuot MH H) = 2 ^ k - 1 := by
    rw [Subgroup.orderOf_coe, hd', MulEquiv.orderOf_eq, hdo, hF]
  obtain ⟨h, hh, hhd⟩ := hd'M
  have hhG : (h : G) ∈ MH ⊓ K := hh
  have hdvd : 2 ^ k - 1 ∣ orderOf (h : G) := by
    rw [← hd'o, ← hhd, Subgroup.orderOf_coe]
    exact orderOf_map_dvd _ h
  have ho0 : orderOf (h : G) ≠ 0 := (orderOf_pos _).ne'
  set y₀ : G := (h : G) ^ (orderOf (h : G) / (2 ^ k - 1)) with hy₀
  have hy₀o : orderOf y₀ = 2 ^ k - 1 := orderOf_pow_orderOf_div ho0 hdvd
  have hy₀M : y₀ ∈ MH := ((MH ⊓ K).pow_mem hhG _).1
  set π : Set Nat.Primes := {p | (p : ℕ) ≠ 2} with hπ
  set Y₀ : Subgroup ↥MH := Subgroup.zpowers ⟨y₀, hy₀M⟩ with hY₀
  have hodd : Odd (2 ^ k - 1) := by
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    exact Nat.Even.sub_odd h1 (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hY₀card : Nat.card Y₀ = 2 ^ k - 1 := by
    rw [hY₀, Nat.card_zpowers, Subgroup.orderOf_mk, hy₀o]
  have hY₀pi : IsPiSubgroup π Y₀ := fun p hp => by
    show (p : ℕ) ≠ 2
    intro h2
    rw [hY₀card, h2] at hp
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hp)
  obtain ⟨H₁, hH₁, hY₀H₁⟩ := CFSG.SolvableHall.solvable_hall_containment hsolv π Y₀ hY₀pi
  have hB' : IsHallSubgroup π (B.subgroupOf MH) := by
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · show (p : ℕ) ≠ 2
      intro h2
      have hc : Nat.card ↥(B.subgroupOf MH) = Nat.card B :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB.1).toEquiv
      rw [hc, h2] at hp
      exact (Nat.not_even_iff_odd.mpr hB.2.1) (even_iff_two_dvd.mpr hp)
    · obtain ⟨j, hj⟩ := hB.2.2
      have hj' : (B.subgroupOf MH).index = 2 ^ j := hj
      rw [hj'] at hp
      have h2 : (p : ℕ) = 2 := (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).mp
        (p.2.dvd_of_dvd_pow hp)
      intro hmem
      exact hmem h2
  obtain ⟨x, hx⟩ := CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable hsolv hH₁ hB'
  have hmem : (x : G) * y₀ * (x : G)⁻¹ ∈ B := by
    have h1 : (MulAut.conj x) ⟨y₀, hy₀M⟩ ∈ B.subgroupOf MH := by
      rw [hx]
      exact Subgroup.mem_map_of_mem _ (hY₀H₁ (Subgroup.mem_zpowers _))
    rw [Subgroup.mem_subgroupOf, MulAut.conj_apply] at h1
    simpa using h1
  refine ⟨Subgroup.zpowers ((x : G) * y₀ * (x : G)⁻¹), Subgroup.zpowers_le.mpr hmem,
    inferInstance, ?_⟩
  have hc : orderOf ((x : G) * y₀ * (x : G)⁻¹) = orderOf y₀ := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  rw [Nat.card_zpowers, hc, hy₀o]

end CFSG.Quasithin.Vol2.Ch11.SecB
