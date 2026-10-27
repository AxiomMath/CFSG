module

public import CFSG.Quasithin.Background.C41PfN
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathAct

public section

namespace CFSG.Quasithin.C41Pf

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_conjAct_mem_autOn {K X W : Subgroup G} (hKN : K ≤ Subgroup.normalizer (W : Set G))
    (hXK : X ≤ K) (hCX : K ⊓ Subgroup.centralizer (W : Set G) ≤ X) {x : G} (hx : x ∈ K)
    (h : conjAct W ⟨x, hKN hx⟩ ∈ autOn X W) : x ∈ X :=
  CFSG.Quasithin.AutOn.mem_of_conjAct_mem_autOn hKN hXK hCX hx h

theorem isParabolic2_autOn {K Q W : Subgroup G} (hKN : K ≤ Subgroup.normalizer (W : Set G))
    (hCO : K ⊓ Subgroup.centralizer (W : Set G) ≤ pCoreOf 2 K) (hQ : IsParabolic2 K Q) :
    IsParabolic2 (autOn K W) (autOn Q W) := by
  obtain ⟨hQK, S, hS, hSQ⟩ := hQ
  have hSK : S ≤ K := hS.1
  have hCS : K ⊓ Subgroup.centralizer (W : Set G) ≤ S :=
    hCO.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS)
  set ρ : ↥K →* MulAut ↥W := (conjAct W).comp (Subgroup.inclusion hKN) with hρ
  have hrange : ρ.range = autOn K W := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKN k, k.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have himage : (S.subgroupOf K).map ρ = autOn S W := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Subgroup.inclusion hKN k, hk, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hSK hx⟩, hx, rfl⟩
  have hSyl := Setup.Wreath.isSylowTwoOf_map_hom hS ρ
  rw [hrange, himage] at hSyl
  refine ⟨autOn_le_autOn hQK, autOn S W, hSyl, ?_⟩
  rintro _ ⟨⟨x, hx, rfl⟩, hxN⟩
  have hxK : (x : G) ∈ K := hx
  refine ⟨x, hSQ ⟨hxK, mem_normalizer_of_map_le ?_⟩, rfl⟩
  rintro _ ⟨s, hs, rfl⟩
  have hsN : s ∈ Subgroup.normalizer (W : Set G) := hKN (hSK hs)
  have hsK : (x : G) * s * (x : G)⁻¹ ∈ K := K.mul_mem (K.mul_mem hxK (hSK hs)) (K.inv_mem hxK)
  have h1 : conjAct W ⟨(x : G) * s * (x : G)⁻¹, hKN hsK⟩ ∈ autOn S W := by
    have h2 : conjAct W ⟨(x : G) * s * (x : G)⁻¹, hKN hsK⟩ =
        conjAct W x * conjAct W ⟨s, hsN⟩ * (conjAct W x)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h2]
    exact (Subgroup.mem_normalizer_iff.mp hxN _).mp ⟨⟨s, hsN⟩, hs, rfl⟩
  simpa [MulAut.conj_apply] using
    mem_of_conjAct_mem_autOn hKN hSK hCS hsK h1

theorem isMaxParabolic2_of_autOn {K P W : Subgroup G} (hKN : K ≤ Subgroup.normalizer (W : Set G))
    (hPK : P ≤ K) (hCP : K ⊓ Subgroup.centralizer (W : Set G) ≤ P)
    (hCO : K ⊓ Subgroup.centralizer (W : Set G) ≤ pCoreOf 2 K)
    (hmax : IsMaxParabolic2 (autOn K W) (autOn P W)) : IsMaxParabolic2 K P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨isParabolic2_of_autOn hKN hPK hCP ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le
    hCO) hmax.1, fun he => hmax.2.1 (by rw [he]), fun Q hQ hQK hPQ => ?_⟩
  have hQK' : Q ≤ K := hQ.1
  have hCQ : K ⊓ Subgroup.centralizer (W : Set G) ≤ Q := hCP.trans hPQ
  have hne : autOn Q W ≠ autOn K W := by
    intro he
    apply hQK
    refine le_antisymm hQK' fun k hk => mem_of_conjAct_mem_autOn hKN hQK' hCQ hk ?_
    rw [he]
    exact ⟨⟨k, hKN hk⟩, hk, rfl⟩
  have heq := hmax.2.2 (autOn Q W) (isParabolic2_autOn hKN hCO hQ) hne (autOn_le_autOn hPQ)
  refine le_antisymm (fun q hq => mem_of_conjAct_mem_autOn hKN hPK hCP (hQK' hq) ?_) hPQ
  rw [← heq]
  exact ⟨⟨q, hKN (hQK' hq)⟩, hq, rfl⟩

end CFSG.Quasithin.C41Pf
