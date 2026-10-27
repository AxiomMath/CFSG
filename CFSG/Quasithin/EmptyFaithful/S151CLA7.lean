module

public import CFSG.Quasithin.EmptyFaithful.S151CLDef
public import CFSG.Quasithin.EmptyFaithful.S151CLPhi
public import CFSG.Quasithin.EmptyFaithful.S151CLA7Alt
public import CFSG.Quasithin.EmptyFaithful.S152VL2
public import CFSG.Quasithin.EmptyFaithful.A38cA7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem s1516_le_normalizer_of_mulEquiv_alt_seven
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hcomp : IsComponentOf L (g1_1516 Z₁)) (e : ↥L ≃* alternatingGroup (Fin 7)) :
    s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := by
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  have hLcomp : L ∈ cComp (g1_1516 Z₁) :=
    Id2519.mem_cComp_of_isComponentIn (DoubleA3.isComponentIn_iff_open.mpr hcomp)
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hLcomp
  rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
      (hSet.pCore_g1_ne_bot hq hMf) hLcomp with hn | ⟨-, h2⟩
  · exact (s1516_le_g1 T Z₁).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn)
  · refine absurd h2 (a7NotA38Type_holds G L ⟨e.toMonoidHom, e.surjective, ?_⟩)
    rw [CLA7.pCore_eq_bot_of_mulEquiv_alt_seven e]
    exact (MonoidHom.ker_eq_bot_iff _).mpr e.injective

theorem exists_noncomm_of_mulEquiv_alt_seven {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (e : ↥L ≃* alternatingGroup (Fin 7)) :
    ∃ a ∈ s1516 T Z₁, ∃ b ∈ s1516 T Z₁, a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hS2, hSi⟩ := lemma_15_1_20_sylow hc.h18.four hc.hL
  set S₀ : Subgroup G := s1516 T Z₁ ⊓ L
  have hP2 : IsPGroup 2 ↥((S₀.subgroupOf L).map (e : ↥L →* alternatingGroup (Fin 7))) :=
    (IsPGroup.of_equiv hS2 (Subgroup.subgroupOfEquivOfLe (inf_le_right : S₀ ≤ L)).symm).map _
  have hPi : ¬ 2 ∣ ((S₀.subgroupOf L).map (e : ↥L →* alternatingGroup (Fin 7))).index := by
    rw [Subgroup.index_map_equiv]
    exact hSi
  obtain ⟨x, hx, y, hy, hxy⟩ := CFSG.Quasithin.R3c9.a7_sylow_two_not_comm (hP2.toSylow hPi)
  rw [IsPGroup.toSylow_coe] at hx hy
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  have hx₁ : (x₀ : G) ∈ S₀ := Subgroup.mem_subgroupOf.mp hx₀
  have hy₁ : (y₀ : G) ∈ S₀ := Subgroup.mem_subgroupOf.mp hy₀
  refine ⟨x₀, hx₁.1, y₀, hy₁.1, fun h => hxy ?_⟩
  have h' : x₀ * y₀ = y₀ * x₀ := Subtype.ext h
  change e x₀ * e y₀ = e y₀ * e x₀
  rw [← map_mul, ← map_mul, h']

theorem false_of_mulEquiv_alt_seven
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hcomp : IsComponentOf L (g1_1516 Z₁)) (hTS : T ≤ Subgroup.normalizer (s1516 T Z₁ : Set G))
    (e : ↥L ≃* alternatingGroup (Fin 7)) : False := by
  have hSN := s1516_le_normalizer_of_mulEquiv_alt_seven h37 h38 hc hcomp e
  obtain ⟨z, hzZ, hz1, l, hlL, hlz⟩ := exists_inner_central_element hc hTS hSN
    (fun α => CLA7.sq_mem_inner_of_mulEquiv_alt_seven e α)
    (exists_noncomm_of_mulEquiv_alt_seven hc e)
  have hyp := hc.h18.six z hzZ hz1
  have hLin : IsComponentIn L (g1_1516 Z₁) := DoubleA3.isComponentIn_iff_open.mpr hcomp
  obtain ⟨-, hcomm, -, hchar⟩ := hyp.component_action hLin
  have hZ : Subgroup.center ↥L = ⊥ := CLA7.center_eq_bot_of_mulEquiv_alt_seven e
  have hL1 : L ≠ ⊥ := by
    intro hL
    have h := Nat.card_congr e.toEquiv
    rw [CFSG.Quasithin.R3c9.card_a7, hL, Subgroup.card_bot] at h
    omega
  obtain ⟨l', hl', hl'1, hl'l', hl'z⟩ := S152V.inner_involution_data hZ
    (sq_eq_one_of_mem_omegaOneCenter T hzZ) hcomm hL1 ⟨l, hlL, hlz⟩
  have heq : L ⊓ Subgroup.centralizer ({z} : Set G) = L ⊓ Subgroup.centralizer ({l'} : Set G) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine and_congr_right fun hx => ⟨fun hxz => ?_, fun hxl => ?_⟩
    · have h1 : z⁻¹ * x * z = x := by
        calc z⁻¹ * x * z = z⁻¹ * (x * z) := by group
          _ = z⁻¹ * (z * x) := by rw [hxz]
          _ = x := by group
      have h2 : l' * x * l' = x := (hl'z x hx).symm.trans h1
      calc x * l' = (l' * x * l') * l' := by rw [h2]
        _ = l' * x * (l' * l') := by group
        _ = l' * x := by rw [hl'l', mul_one]
    · have h1 : z⁻¹ * x * z = x := by
        rw [hl'z x hx]
        calc l' * x * l' = x * l' * l' := by rw [hxl]
          _ = x * (l' * l') := by group
          _ = x := by rw [hl'l', mul_one]
      calc x * z = z * (z⁻¹ * x * z) := by group
        _ = z * x := by rw [h1]
  rw [heq] at hchar
  exact CLA7.not_charTwo_centralizer_of_mulEquiv_alt_seven e hl' hl'1 hl'l' hchar

theorem compListNoA7_holds
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) : CompListNoA7 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hx ⟨e⟩
  exact false_of_mulEquiv_alt_seven h37 h38 hc hcomp hx.s_normal e

end CFSG.Quasithin
