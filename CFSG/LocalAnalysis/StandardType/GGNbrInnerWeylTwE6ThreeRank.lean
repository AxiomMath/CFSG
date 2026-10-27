module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6ThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint

namespace NbrTwE6Three

theorem exists_pGroup_lift {H M : Type*} [Group H] [Finite H] [Group M] (ρ : H →* M) {p : ℕ}
    [Fact p.Prime] {E : Subgroup M} (hE : IsPGroup p E) (hEr : E ≤ ρ.range) {y : H}
    (hy : y ∈ Subgroup.center H) (hyp : y ^ p = 1) (hyρ : ρ y = 1) (hy1 : y ≠ 1) :
    ∃ P : Subgroup H, IsPGroup p P ∧ P ≤ E.comap ρ ∧ p * Nat.card E ≤ Nat.card P := by
  classical
  have hyÊ : y ∈ E.comap ρ := by
    rw [Subgroup.mem_comap, hyρ]
    exact E.one_mem
  obtain ⟨P₀⟩ : Nonempty (Sylow p (E.comap ρ)) := inferInstance
  set ŷ : E.comap ρ := ⟨y, hyÊ⟩ with hŷ
  have hŷc : ŷ ∈ Subgroup.center (E.comap ρ) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hy g.1)
  haveI hYn : (Subgroup.zpowers ŷ).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hŷc)
  have hŷp : ŷ ^ p = 1 := Subtype.ext (by simpa [hŷ] using hyp)
  have hŷ1 : ŷ ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hord : orderOf ŷ = p := orderOf_eq_prime hŷp hŷ1
  have hYp : IsPGroup p (Subgroup.zpowers ŷ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hYP : Subgroup.zpowers ŷ ≤ (P₀ : Subgroup (E.comap ρ)) := hYp.le_sylow_of_normal P₀
  let f : E.comap ρ →* E := (ρ.comp (E.comap ρ).subtype).codRestrict E (fun g => g.2)
  have hf : Function.Surjective f := by
    intro e
    obtain ⟨h, hh⟩ := hEr e.2
    exact ⟨⟨h, by rw [Subgroup.mem_comap, hh]; exact e.2⟩, Subtype.ext hh⟩
  have hQ : ((P₀.mapSurjective hf : Sylow p E) : Subgroup E) = ⊤ :=
    ((P₀.mapSurjective hf).is_maximal' (hE.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at hQ
  let g : (P₀ : Subgroup (E.comap ρ)) →* E := f.comp (P₀ : Subgroup (E.comap ρ)).subtype
  have hg : Function.Surjective g := by
    intro e
    have : e ∈ (P₀ : Subgroup (E.comap ρ)).map f := by rw [hQ]; exact Subgroup.mem_top e
    obtain ⟨a, ha, hae⟩ := this
    exact ⟨⟨a, ha⟩, hae⟩
  have hcard := Subgroup.card_ker_mul_card_of_surjective hg
  set ŷ0 : (P₀ : Subgroup (E.comap ρ)) := ⟨ŷ, hYP (Subgroup.mem_zpowers ŷ)⟩ with hŷ0def
  have hŷ0 : ŷ0 ∈ g.ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext hyρ
  have hŷ0p : ŷ0 ^ p = 1 := Subtype.ext (Subtype.ext (by simpa [hŷ0def, hŷ] using hyp))
  have hŷ01 : ŷ0 ≠ 1 := fun h => hŷ1 (congrArg Subtype.val h)
  have hcardz : Nat.card (Subgroup.zpowers ŷ0) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hŷ0p hŷ01]
  have hker : p ≤ Nat.card g.ker :=
    calc p = Nat.card (Subgroup.zpowers ŷ0) := hcardz.symm
      _ ≤ Nat.card g.ker := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hŷ0)
  refine ⟨(P₀ : Subgroup (E.comap ρ)).map (E.comap ρ).subtype, P₀.isPGroup'.map _, ?_, ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    exact a.2
  · rw [Subgroup.card_map_of_injective (E.comap ρ).subtype_injective, ← hcard]
    exact Nat.mul_le_mul_right _ hker

theorem eq_one_of_mem_center {K : Type*} [Group K] {p : ℕ} [Fact p.Prime]
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) {c : K} (hc : c ∈ Subgroup.center K) {k : ℕ}
    (hck : c ^ p ^ k = 1) : c = 1 := by
  have h1 : orderOf c ∣ p ^ k := orderOf_dvd_of_pow_eq_one hck
  have h2 : orderOf c ∣ Nat.card (Subgroup.center K) := by
    have := orderOf_dvd_natCard (⟨c, hc⟩ : Subgroup.center K)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (p ^ k) (Nat.card (Subgroup.center K)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hZ)
  have : orderOf c = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h2)
  exact orderOf_eq_one_iff.mp this

end NbrTwE6Three

@[expose] def GGTwoLocalRankDom (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) :
    Prop :=
  ∀ E : Subgroup (MulAut L'), E ≤ A ⊔ (MulAut.conj : L' →* MulAut L').range →
    IsElemAbelian p E → GGTwoLocalAut E → Nat.card E ≤ Nat.card A

section Config

open NbrTwE6Three

variable {G : Type} [Group G] [Finite G]

theorem ggTwoLocalRankDom_ggGamma {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) :
    GGTwoLocalRankDom p (ggGamma K hN).range := by
  classical
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  haveI := Fact.mk hp
  intro E hEle hE hEloc
  obtain ⟨U, hU, hU2, hUE⟩ := hEloc
  have hS : LargeEvenSHat p B y K := hnb.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hN
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hS.2.2.2.1
  have hyBs : y ∈ Bs := hBBs hS.2.1
  have hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    TableB.IsElemAbelian.comm hBs ha hb
  have hH : Bs ⊔ K ≤ Subgroup.normalizer (K : Set G) := sup_le hN Subgroup.le_normalizer
  set ρ := ggGamma K hH with hρ
  have hρb : ∀ (b : G) (hb : b ∈ Bs), ρ ⟨b, Subgroup.mem_sup_left hb⟩ = ggGamma K hN ⟨b, hb⟩ :=
    fun b hb => rfl
  have hρk : ∀ (k : G) (hk : k ∈ K),
      ρ ⟨k, Subgroup.mem_sup_right hk⟩ = MulAut.conj (⟨k, hk⟩ : K) := fun k hk =>
    normalizerMonoidHom_of_mem K ⟨k, hk⟩
  have hEρ : E ≤ ρ.range := by
    refine hEle.trans (sup_le ?_ ?_)
    · rintro _ ⟨b, rfl⟩
      exact ⟨⟨b, Subgroup.mem_sup_left b.2⟩, hρb b b.2⟩
    · rintro _ ⟨k, rfl⟩
      exact ⟨⟨k, Subgroup.mem_sup_right k.2⟩, hρk k k.2⟩
  have hEp : IsPGroup p E := TableB.isPGroup_of_isElemAbelian hE
  have hyH : y ∈ Bs ⊔ K := Subgroup.mem_sup_left hyBs
  have hyK : ∀ k ∈ K, k * y = y * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKy hk)
  have hHy : Bs ⊔ K ≤ Subgroup.centralizer ({y} : Set G) :=
    sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hBc b hb y hyBs)) hKy
  have hy' : (⟨y, hyH⟩ : ↥(Bs ⊔ K)) ∈ Subgroup.center ↥(Bs ⊔ K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hHy g.2))
  have hyp : (⟨y, hyH⟩ : ↥(Bs ⊔ K)) ^ p = 1 :=
    Subtype.ext (by simpa using hBs.2 y hyBs)
  have hyρ : ρ ⟨y, hyH⟩ = 1 := by
    rw [hρ, ggGamma_eq_one_iff]
    exact Subgroup.mem_centralizer_iff.mpr fun k hk => hyK k hk
  have hy1 : (⟨y, hyH⟩ : ↥(Bs ⊔ K)) ≠ 1 := fun h => hS.2.2.1 (congrArg Subtype.val h)
  obtain ⟨P, hPp, hPE, hPcard⟩ :=
    NbrTwE6Three.exists_pGroup_lift ρ hEp hEρ hy' hyp hyρ hy1
  have hPpg : ∀ w ∈ P, ∃ k : ℕ, w ^ p ^ k = 1 := fun w hw => by
    obtain ⟨k, hk⟩ := hPp ⟨w, hw⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hK1 : ∀ w ∈ P, (w : G) ∈ K → ρ w = 1 → w = 1 := by
    intro w hwP hwK hρw
    have hcent : (w : G) ∈ Subgroup.centralizer (K : Set G) :=
      (ggGamma_eq_one_iff K hH w).mp hρw
    have hcK : (⟨(w : G), hwK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcent g g.2)
    obtain ⟨k, hk⟩ := hPpg w hwP
    have h1 : (⟨(w : G), hwK⟩ : K) ^ p ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h0 : (⟨(w : G), hwK⟩ : K) = 1 := eq_one_of_mem_center hZ hcK h1
    exact Subtype.ext (by simpa using congrArg Subtype.val h0)
  have hcomm : ∀ u ∈ P, ∀ v ∈ P, (u : G) * v = v * u := by
    intro u hu v hv
    have hc : u * v * u⁻¹ * v⁻¹ = 1 := by
      refine hK1 _ (P.mul_mem (P.mul_mem (P.mul_mem hu hv) (P.inv_mem hu)) (P.inv_mem hv)) ?_ ?_
      · have h1 := CFSG.SeitzReduction.F4Pilot.commutator_sup_le_of_comm_of_le_normalizer hBc hN
          (Subgroup.commutator_mem_commutator u.2 v.2)
        simpa [commutatorElement_def] using h1
      · have huv := TableB.IsElemAbelian.comm hE (Subgroup.mem_comap.mp (hPE hu))
          (Subgroup.mem_comap.mp (hPE hv))
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, huv]
        group
    have huv : u * v = v * u := by
      have h1 : u * v * u⁻¹ = v := mul_inv_eq_one.mp hc
      calc u * v = (u * v * u⁻¹) * u := by group
        _ = v * u := by rw [h1]
    exact congrArg Subtype.val huv
  have hpow : ∀ u ∈ P, (u : G) ^ p = 1 := by
    intro u hu
    have h1 : u ^ p = 1 := by
      refine hK1 _ (P.pow_mem hu p) ?_ ?_
      · have hu' : (u : G) ∈ K ⊔ Bs := by
          rw [sup_comm]
          exact u.2
        simpa using CFSG.StandardType.pow_mem_of_mem_sup hN (fun b hb => hBs.2 b hb) hu'
      · rw [map_pow]
        exact hE.2 _ (Subgroup.mem_comap.mp (hPE hu))
    simpa using congrArg Subtype.val h1
  set P' : Subgroup G := P.map (Bs ⊔ K).subtype with hP'
  have hP'ab : IsElemAbelian p P' := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, u, hu, rfl⟩ ⟨_, v, hv, rfl⟩
      exact Subtype.ext (hcomm u hu v hv)
    · rintro _ ⟨u, hu, rfl⟩
      exact hpow u hu
  have hU' : ∀ g ∈ P', ∀ u ∈ U.map K.subtype, g * u * g⁻¹ ∈ U.map K.subtype := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨z, hz, rfl⟩
    have h1 := hUE (ρ g) (Subgroup.mem_comap.mp (hPE hg)) z hz
    exact ⟨ρ g z, h1, ggGamma_coe K hH g z⟩
  have hPU : P' ≤ Subgroup.normalizer ((U.map K.subtype : Subgroup G) : Set G) := fun g hg =>
    CFSG.StandardType.mem_normalizer_of_forall_conj_mem fun w hw => by
      simpa using hU' g⁻¹ (P'.inv_mem hg) w hw
  have hUne : U.map K.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective]
    exact hU
  have hTL : IsTwoLocal (Subgroup.normalizer ((U.map K.subtype : Subgroup G) : Set G)) :=
    ⟨_, hUne, hU2.map _, rfl⟩
  have h1 : Nat.card P' ≤ p ^ LargeEvenTwoLocalRank p G :=
    TableB.card_le_of_twoLocal hp hTL hPU hP'ab
  have hcA := card_range_ggGamma_mul_of_sHat hp hS hBN
  have hle : Nat.card (ggGamma K hBN).range ≤ Nat.card (ggGamma K hN).range := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  have hP'card : Nat.card P' = Nat.card P :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have h2 : p * Nat.card E ≤ p * Nat.card (ggGamma K hN).range :=
    calc p * Nat.card E ≤ Nat.card P := hPcard
      _ = Nat.card P' := hP'card.symm
      _ ≤ p ^ LargeEvenTwoLocalRank p G := h1
      _ = Nat.card B := hS.1.2.1.symm
      _ = Nat.card (ggGamma K hBN).range * p := hcA.symm
      _ ≤ Nat.card (ggGamma K hN).range * p := Nat.mul_le_mul_right _ hle
      _ = p * Nat.card (ggGamma K hN).range := mul_comm _ _
  exact Nat.le_of_mul_le_mul_left h2 hp.pos

end Config

end CFSG.StandardType

end
