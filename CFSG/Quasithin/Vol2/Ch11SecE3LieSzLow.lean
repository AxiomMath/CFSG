module

public import CFSG.Quasithin.Vol2.Ch11SecE3LieLow
public import CFSG.Quasithin.Vol2.Ch11SecE3LieSzGen
public import CFSG.Quasithin.Vol2.Ch11SecE3Sz
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b CFSG.LieType.Ree
open scoped Pointwise

section Transport

variable {G : Type} [Group G] [Finite G]

theorem le_nParam_of_suzuki {L T : Subgroup G} {a : ℕ} {K : Type} [Field K] [Finite K]
    (h : AlmostSimple L) (hT : quasithinIsSylowTwo T) (hLT : L ⊔ T = ⊤)
    (e : ↥L ≃* suzukiGroup a K) (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ((2 * a + 1 : ℕ) : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  have hLn := h.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_suzukiGroup hK
  set U : Subgroup G := T ⊓ L with hUdef
  set ψ : suzukiGroup a K →* G := L.subtype.comp e.symm.toMonoidHom with hψdef
  have hψi : Function.Injective ψ := L.subtype_injective.comp e.symm.injective
  have hψr : ψ.range = L := by
    rw [hψdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set P : Subgroup (suzukiGroup a K) := U.comap ψ with hPdef
  have hUP : P.map ψ = U := Subgroup.map_comap_eq_self (hψr ▸ inf_le_right)
  have hP2 : IsPGroup 2 P := IsPGroup.comap_of_injective (hT.1.to_inf_left) ψ hψi
  have hPidx : ¬ 2 ∣ P.index := by
    obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal (hT.1.toSylow hT.2) (N := L)
    have hQidx := Q.not_dvd_index
    have e1 : P = (U.subgroupOf L).comap e.symm.toMonoidHom := by
      rw [hPdef, hψdef, ← Subgroup.comap_comap]
      rfl
    rw [e1, Subgroup.index_comap_of_surjective _ e.symm.surjective]
    rwa [hQ] at hQidx
  obtain ⟨g, hg⟩ : ∃ g : suzukiGroup a K, A1b.conjSub g (suzukiU a K) = P := by
    let P0 := Sylow.ofCard (suzukiU a K) (CFSG.RankThree.card_suzukiU_eq hK)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (suzukiGroup a K) P0 (hP2.toSylow hPidx)
    refine ⟨g, ?_⟩
    ext x
    have h1 := CFSG.RankThree.mem_smul_sylow_iff P0 g x
    rw [hg] at h1
    rw [A1b.mem_conjSub_iff]
    exact h1.symm
  set A : Subgroup G := (A1b.conjSub g (suzukiZ0 a K)).map ψ with hAdef
  have hAU : A ≤ U := by
    rw [← hUP, ← hg]
    exact Subgroup.map_mono (A1b.conjSub_mono g suzukiZ0_le_suzukiU)
  have hA : IsElemAbelian 2 A := isElemAbelian_map' ψ (isElemAbelian_map' _
    (isElemAbelian_suzukiZ0 hK))
  have hAcard : Nat.card A = 2 ^ (2 * a + 1) := by
    rw [hAdef, Subgroup.card_map_of_injective hψi, card_conjSub, card_suzukiZ0 hK, hK]
  have hA1 : A ≠ ⊥ := by
    intro h0
    have h1 : Nat.card A = 1 := by rw [h0, Subgroup.card_bot]
    have h2 : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
    rw [h1] at hAcard
    exact absurd hAcard h2.ne
  have hUA : U ≤ Subgroup.centralizer (A : Set G) := by
    rw [← hUP, ← hg]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hxy := (suzuki_unipotent_structure hK).2.2.2.2.2.1 y hy x hx
    rw [← map_mul ψ, ← map_mul ψ, ← map_mul, ← map_mul, hxy]
  have huniq : ∀ x : G, A1b.conjSub x A ≤ T → A1b.conjSub x A = A := by
    intro x hx
    have hxL : A1b.conjSub x A ≤ L := by
      rintro _ ⟨u, hu, rfl⟩
      show x * u * x⁻¹ ∈ L
      exact hLn.conj_mem u (hAU hu).2 x
    have hxU : A1b.conjSub x A ≤ U := le_inf hx hxL
    have hle : A1b.conjSub x A ≤ A := by
      intro z hz
      have hz2 : z ^ 2 = 1 := (isElemAbelian_map' _ hA).2 z hz
      have hzU : z ∈ U := hxU hz
      rw [← hUP, ← hg] at hzU
      obtain ⟨w, hw, rfl⟩ := hzU
      have hw' : g⁻¹ * w * g ∈ suzukiU a K := A1b.mem_conjSub_iff.mp hw
      have hwsq : w ^ 2 = 1 := hψi (by rw [map_pow, hz2, map_one])
      have hw2 : (g⁻¹ * w * g) ^ 2 = 1 := by
        rw [sq] at hwsq ⊢
        rw [show g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g by group, hwsq]
        group
      by_cases hw1 : g⁻¹ * w * g = 1
      · have hw0 : w = 1 := by
          have := congrArg (fun y => g * y * g⁻¹) hw1
          simpa [mul_assoc] using this
        rw [hw0, map_one]
        exact A.one_mem
      · obtain ⟨v, -, hv⟩ := CFSG.RankThree.eq_suzukiSElt_zero_of_sq_eq_one hK hw' hw2 hw1
        refine ⟨w, ?_, rfl⟩
        rw [SetLike.mem_coe, A1b.mem_conjSub_iff, hv]
        exact (mem_suzukiZ0_iff hK).2 ⟨v, rfl⟩
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_conjSub]
  have hNA : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    intro x hx
    rw [← A1b.conjSub_eq_iff_mem_normalizer]
    refine huniq x ((A1b.conjSub_mono x hAU).trans ?_)
    rw [A1b.conjSub_eq_iff_mem_normalizer.mpr hx]
    exact inf_le_left
  have hgen : ∀ l ∈ L, A1b.conjSub l U ≠ U → L ≤ U ⊔ A1b.conjSub l U := by
    intro l hl hne
    set M : suzukiGroup a K := e ⟨l, hl⟩ with hM
    have hψM : ψ M = l := by simp [hψdef, hM]
    have hcU : A1b.conjSub l U = (A1b.conjSub M P).map ψ := by
      rw [map_conjSub, hψM, hUP]
    have hMP : A1b.conjSub M P ≠ P := fun hc => hne (by rw [hcU, hc, hUP])
    have e1 : A1b.conjSub M P = A1b.conjSub g (A1b.conjSub (g⁻¹ * M * g) (suzukiU a K)) := by
      rw [← hg, ← A1b.conjSub_mul, ← A1b.conjSub_mul]
      congr 1
      group
    have hM' : A1b.conjSub (g⁻¹ * M * g) (suzukiU a K) ≠ suzukiU a K := fun hc =>
      hMP (by rw [e1, hc, hg])
    have hPtop : P ⊔ A1b.conjSub M P = ⊤ := by
      rw [e1, ← hg, ← conjSub_sup, suzukiU_sup_conj_eq_top hK hM', conjSub_top]
    rw [hcU, ← hUP, ← Subgroup.map_sup, hPtop, ← MonoidHom.range_eq_map, hψr]
  exact le_nParam_of_almostSimple h ⟨le_top, hT.1, by rw [Subgroup.relIndex_top_right]; exact hT.2⟩
    hLT inf_le_left hAU inf_le_right hA hA1 hAcard (by omega) hUA huniq le_normalizer_inf hNA hgen

theorem le_nParam_of_isSz {T : Subgroup G} {n : ℕ} (hSz : IsSz n ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : (n : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hSz
  have hnab : ∃ x y : ↥(CFSG.generalizedFitting G), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := suzuki_nonabelian ha hK
    refine ⟨e.symm x, e.symm y, fun hc => hxy ?_⟩
    simpa using congrArg e hc
  exact le_nParam_of_suzuki (almostSimple_generalizedFitting hs hnab hT.1 hFT) hT hFT e ha hK

theorem nParam_eq_of_isSz {T : Subgroup G} {n : ℕ} (hSz : IsSz n ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) = n :=
  le_antisymm (nParam_le_of_isSz hSz hs hT hFT) (le_nParam_of_isSz hSz hs hT hFT)

end Transport

end CFSG.Quasithin.Vol2.Ch11.SecE3
