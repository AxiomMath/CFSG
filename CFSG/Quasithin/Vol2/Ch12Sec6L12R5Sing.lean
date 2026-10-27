module

public import CFSG.Quasithin.Vol2.Ch12Sec6L69

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

private theorem T_le_normalizer_V' (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    T ≤ Subgroup.normalizer (V : Set G) := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  exact (hall V hyp.irrPlus).1.2.1

theorem ne_one_of_hasWt_four {y : D8} (h : HasWt 4 y) : y ≠ 1 := by
  rintro rfl
  obtain ⟨m, hm, hw⟩ := h
  rw [S126FE.mk_eq_one_iff] at hm
  rcases hm with rfl | rfl
  · exact absurd hw (by decide)
  · exact absurd hw (by decide)

theorem charTwo_centralizer_singular (h1222 : Stmt12_2_2) {F : Frame126 T L V}
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {u : G} (hu : u ∈ V)
    (hs : HasWt 4 (F.β ⟨u, hu⟩)) :
    CharTwo (Subgroup.centralizer ({u} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  obtain ⟨S, hS, hSu⟩ := S126L19.central_of_wt4 F hH (T_le_normalizer_V' h1222 hH) hZ
    (u := ⟨u, hu⟩) hs
  obtain ⟨-, hVe⟩ := V_facts h1222 hH
  have hu1 : u ≠ 1 := by
    intro h
    have h1 : F.β ⟨u, hu⟩ = 1 := by
      rw [show (⟨u, hu⟩ : ↥V) = 1 from Subtype.ext h, map_one]
    exact ne_one_of_hasWt_four hs h1
  have hu2 : u ^ 2 = 1 := hVe.2 u hu
  have huG : u ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hN : Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    intro y hy
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hy).symm k).symm).eq.symm
  have hzp : IsPGroup 2 (Subgroup.zpowers u) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hu2 hu1]
    norm_num
  have hle : Subgroup.zpowers u ≤ pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 (Subgroup.zpowers_le.mpr huG) hN hzp
  have hO2 : pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ≠ ⊥ := by
    intro hbot
    rw [hbot, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
    exact hu1 hle
  have hS2 : ¬ 2 ∣ S.index := fun h => hS.2 h
  let S' : Sylow 2 G := hS.1.toSylow hS2
  have hInH : InH (S' : Subgroup G) (Subgroup.centralizer ({u} : Set G)) := And.intro hSu hO2
  have hEven : CFSG.Open.quasithinEvenCharacteristic G := hyp.qtke.2.1
  exact charTwo_of_inH hEven S' hInH

theorem charTwo_inf_centralizer_of_comm {K : Subgroup G} {u v : G}
    (hu : CharTwo (Subgroup.centralizer ({u} : Set G))) (hvu : u * v = v * u) (hv2 : v ^ 2 = 1)
    (hv1 : v ≠ 1) (hKv : K ≤ Subgroup.centralizer ({v} : Set G))
    (hKn : Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (K : Set G)) :
    CharTwo (K ⊓ Subgroup.centralizer ({u} : Set G)) := by
  have hvC : Subgroup.zpowers v ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hvu.symm
  have hzp : IsPGroup 2 (Subgroup.zpowers v) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hv2 hv1]
    norm_num
  have h1 := hu.inf_centralizer hvC hzp
  have e : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) =
      Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [e] at h1
  have hle : K ⊓ Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({v} : Set G) :=
    fun x hx => ⟨hx.2, hKv hx.1⟩
  have hnorm : ((K ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf
      (Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({v} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    rintro h g ⟨hhK, hhC⟩ ⟨hgC, hgv⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hKn hgv) h).mp hhK, ?_⟩
    have hh := Subgroup.mem_centralizer_singleton_iff.mp hhC
    have hg := Subgroup.mem_centralizer_singleton_iff.mp hgC
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc g * h * g⁻¹ * u = g * h * (g⁻¹ * u) := by group
      _ = g * h * (u * g⁻¹) := by
        congr 1
        calc g⁻¹ * u = g⁻¹ * (u * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * u) * g⁻¹ := by rw [hg]
          _ = u * g⁻¹ := by group
      _ = g * (h * u) * g⁻¹ := by group
      _ = g * (u * h) * g⁻¹ := by rw [hh]
      _ = u * (g * h * g⁻¹) := by
        calc g * (u * h) * g⁻¹ = (g * u) * h * g⁻¹ := by group
          _ = (u * g) * h * g⁻¹ := by rw [hg]
          _ = u * (g * h * g⁻¹) := by group
  exact CharTwo.of_normal h1 hle hnorm

end S126T2

end CFSG.Quasithin.H13
