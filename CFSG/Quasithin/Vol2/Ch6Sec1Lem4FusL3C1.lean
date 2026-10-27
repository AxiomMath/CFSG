module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3Lev

public section

namespace CFSG.Quasithin.H13

open CFSG.GorensteinWalter CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem kg614FusionL2_of_psl2_prime {Γ : Type} [Group Γ] [Finite Γ] (K T X : Subgroup Γ)
    {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p)
    (ϕ : ModO2 K ≃* PSL2 F)
    (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) (hTs : IsSylowTwoOf T (K ⊔ T))
    (hXK : X ≤ K) (hXO : X = oTwoUpper X) (hX5 : (X ⊓ T).relIndex X = 5)
    (hXn : ((X ⊓ T).subgroupOf X).Normal) (hTX : T ≤ Subgroup.normalizer (X : Set Γ))
    {E : Subgroup Γ} (hE : E ≤ pCoreOf 2 (X ⊔ T)) (hEa : IsElemAbelian 2 E)
    (hEK : ¬ E ≤ pCoreOf 2 (K ⊔ T)) :
    ∃ k ∈ K, E.map (MulAut.conj k).toMonoidHom ≤ T ∧
      ¬ E.map (MulAut.conj k).toMonoidHom ≤ pCoreOf 2 (X ⊔ T) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hKo : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by rw [hF, pow_one]⟩
  have hcard : 3 < Nat.card F := by
    rw [hF]
    omega
  have hF1 : Nat.card F = p ^ 1 := by rw [hF, pow_one]
  have hZ : Subgroup.center (ModO2 K) = ⊥ := center_eq_bot_of_mulEquiv_psl2_614 ϕ
  have hfieldF : FieldFus614 F := fieldFus614_of_card_prime hp hF
  have hlocP := locFus614_pGammaL2 hKo hcard hfieldF
  let Ψ : MulAut (ModO2 K) ≃* PGammaL2 F :=
    (MulAut.congr ϕ).trans (pGammaL2EquivMulAut614 F hKo hcard hF1).symm
  have hΨ : ((MulAut.conj : ModO2 K →* MulAut (ModO2 K)).range).map Ψ.toMonoidHom =
      pGammaL2PSLRange F := by
    have e : Ψ.toMonoidHom = (pGammaL2EquivMulAut614 F hKo hcard hF1).symm.toMonoidHom.comp
        (MulAut.congr ϕ).toMonoidHom := rfl
    rw [e, ← Subgroup.map_map, map_mulAut_congr614, map_pGammaL2EquivMulAut614]
  have : Finite (MulAut (ModO2 K)) :=
    Finite.of_injective (fun f : MulAut (ModO2 K) => (f : ModO2 K → ModO2 K))
      DFunLike.coe_injective
  have hloc := locFus614_of_mulEquiv Ψ hΨ hlocP
  exact kg614Fusion_conclusion_of_locFus hZ hloc hTK hTs hXK hXO hX5 hXn hTX hE hEa hEK

theorem le_centralizer_of_le_pCoreOf_levi614 {G : Type} [Group G] [Finite G] {K T E : Subgroup G}
    {z : G} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hK : IsL3Levi K z p)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hE : E ≤ pCoreOf 2 (K ⊔ T)) :
    E ≤ Subgroup.centralizer (K : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpc : CFSG.pCore 2 ↥K = Subgroup.center ↥K := IsL3Levi.pCore_eq_center hp hp5 hK
  have hperf : Group.IsPerfect ↥K := by
    obtain ⟨-, -, -, hpf, -⟩ := hK
    exact hpf
  have hYK : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hYO : K ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T)
  have hOp : IsPGroup 2 (pCoreOf 2 (K ⊔ T)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ T)
  have hKO : K ≤ Subgroup.normalizer ((pCoreOf 2 (K ⊔ T) ⊓ K : Subgroup G) : Set G) := by
    intro g hg
    have hgY : g ∈ K ⊔ T := Subgroup.mem_sup_left hg
    have h1 := Subgroup.mem_normalizer_iff.mp (hYO hgY)
    have h2 := Subgroup.mem_normalizer_iff.mp (hYK hgY)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have e1 := h1 h
    have e2 := h2 h
    simp only [SetLike.mem_coe, Subgroup.mem_inf] at e1 e2 ⊢
    exact and_congr e1 e2
  have hOK : pCoreOf 2 (K ⊔ T) ⊓ K ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hKO (hOp.to_le inf_le_left)
  intro e he
  have heO : e ∈ pCoreOf 2 (K ⊔ T) := hE he
  have heY : e ∈ K ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 (K ⊔ T) heO
  have heN : e ∈ Subgroup.normalizer (K : Set G) := hYK heY
  obtain ⟨α, hα⟩ : ∃ α : ↥K → ↥K, ∀ k : ↥K, (α k : G) = e * (k : G) * e⁻¹ :=
    ⟨fun k => ⟨e * (k : G) * e⁻¹, (Subgroup.mem_normalizer_iff.mp heN k).mp k.2⟩, fun k => rfl⟩
  refine centralizer_mem_of_perfect_action614 hperf heN α hα ?_
  intro k
  rw [← hpc]
  have hval : (((α k)⁻¹ * k : ↥K) : G) = e * ((k : G)⁻¹ * e⁻¹ * (k : G)) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hα]
    group
  have hkY : (k : G) ∈ K ⊔ T := Subgroup.mem_sup_left k.2
  have hconj : (k : G)⁻¹ * e⁻¹ * (k : G) ∈ pCoreOf 2 (K ⊔ T) := by
    refine (Subgroup.mem_normalizer_iff.mp (hYO hkY) ((k : G)⁻¹ * e⁻¹ * (k : G))).mpr ?_
    have hc : (k : G) * ((k : G)⁻¹ * e⁻¹ * (k : G)) * (k : G)⁻¹ = e⁻¹ := by group
    rw [hc]
    exact (pCoreOf 2 (K ⊔ T)).inv_mem heO
  have hmemO : (((α k)⁻¹ * k : ↥K) : G) ∈ pCoreOf 2 (K ⊔ T) := by
    rw [hval]
    exact (pCoreOf 2 (K ⊔ T)).mul_mem heO hconj
  have hmem : (((α k)⁻¹ * k : ↥K) : G) ∈ pCoreOf 2 K :=
    hOK (Subgroup.mem_inf.mpr ⟨hmemO, ((α k)⁻¹ * k).2⟩)
  unfold pCoreOf at hmem
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp hmem
  have hx' : (α k)⁻¹ * k = x := Subtype.ext hxe.symm
  rw [hx']
  exact hx

end CFSG.Quasithin.H13
