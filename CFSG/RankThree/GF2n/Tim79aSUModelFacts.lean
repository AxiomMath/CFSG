module

public import CFSG.RankThree.GF2n.Tim79aSUStatements
public import CFSG.RankThree.GF2n.Tim79aSec33Defs
public import CFSG.RankThree.GF2n.Tim79aSURootDisjoint
public import CFSG.Timmesfeld.Transvection.ModelSUCentre
public import CFSG.Timmesfeld.Transvection.AssembleRel
public import CFSG.Timmesfeld.Transvection.ModelSUCount

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed

@[expose] def SUModelDisjoint : Prop :=
  ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), Nat.card F = (2 ^ f) ^ 2 →
    4 ≤ m → ∀ (K : Type) [Group K] (Φ : SU (unitaryInvolution F 2 f) m →* K),
      Function.Surjective Φ → Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m) →
      ∀ (a : Fin m → F) (T : Subgroup (SU (unitaryInvolution F 2 f) m)), a ≠ 0 →
        uForm (unitaryInvolution F 2 f) a a = 0 → IsUTransGroup (unitaryInvolution F 2 f) a T →
        ∀ g : K, conjSub (T.map Φ) g ≤ Subgroup.centralizer ((T.map Φ : Subgroup K) : Set K) →
          conjSub (T.map Φ) g ≠ T.map Φ →
          conjSub (T.map Φ) g ⊓
            pCoreOf 2 (Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)) = ⊥

@[expose] def SUModelMoves : Prop :=
  ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), Nat.card F = (2 ^ f) ^ 2 →
    4 ≤ m → ∀ (K : Type) [Group K] (Φ : SU (unitaryInvolution F 2 f) m →* K),
      Function.Surjective Φ → Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m) →
      ∀ (a : Fin m → F) (T : Subgroup (SU (unitaryInvolution F 2 f) m)), a ≠ 0 →
        uForm (unitaryInvolution F 2 f) a a = 0 → IsUTransGroup (unitaryInvolution F 2 f) a T →
        ∃ g : K, conjSub (T.map Φ) g ≤ Subgroup.centralizer ((T.map Φ : Subgroup K) : Set K) ∧
          conjSub (T.map Φ) g ≠ T.map Φ ∧
          ∃ x ∈ pCoreOf 2 (Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)),
            ∃ t ∈ conjSub (T.map Φ) g, x * t ≠ t * x

@[expose] def SUModelCenter : Prop :=
  ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), Nat.card F = (2 ^ f) ^ 2 →
    4 ≤ m → ∀ (K : Type) [Group K] (Φ : SU (unitaryInvolution F 2 f) m →* K),
      Function.Surjective Φ → Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m) →
      ∀ (a : Fin m → F) (T : Subgroup (SU (unitaryInvolution F 2 f) m)), a ≠ 0 →
        uForm (unitaryInvolution F 2 f) a a = 0 → IsUTransGroup (unitaryInvolution F 2 f) a T →
        ∀ x ∈ pCoreOf 2 (Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)),
          (∀ y ∈ pCoreOf 2 (Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)),
            x * y = y * x) → x ∈ T.map Φ

@[expose] def SUModelCard : Prop :=
  ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), Nat.card F = (2 ^ f) ^ 2 →
    4 ≤ m → ∀ (K : Type) [Group K] (Φ : SU (unitaryInvolution F 2 f) m →* K),
      Function.Surjective Φ → Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m) →
      ∀ (a : Fin m → F) (T : Subgroup (SU (unitaryInvolution F 2 f) m)), a ≠ 0 →
        uForm (unitaryInvolution F 2 f) a a = 0 → IsUTransGroup (unitaryInvolution F 2 f) a T →
        Nat.card ↥(T.map Φ) = 2 ^ f

@[expose] def SUModelCount : Prop :=
  ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), Nat.card F = (2 ^ f) ^ 2 →
    4 ≤ m → ∀ (K : Type) [Group K] (Φ : SU (unitaryInvolution F 2 f) m →* K),
      Function.Surjective Φ → Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m) →
      ∀ (a : Fin m → F) (T : Subgroup (SU (unitaryInvolution F 2 f) m)), a ≠ 0 →
        uForm (unitaryInvolution F 2 f) a a = 0 → IsUTransGroup (unitaryInvolution F 2 f) a T →
        ∃ S : Finset K, (2 ^ f) ^ (2 * m - 3) ≤ S.card ∧
          Set.InjOn (fun g => conjSub (T.map Φ) g) (S : Set K)

@[expose] def SUModelGen : Prop :=
  ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), Nat.card F = (2 ^ f) ^ 2 →
    4 ≤ m → ∀ (K : Type) [Group K] (Φ : SU (unitaryInvolution F 2 f) m →* K),
      Function.Surjective Φ → Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m) →
      ∀ (a : Fin m → F) (T : Subgroup (SU (unitaryInvolution F 2 f) m)), a ≠ 0 →
        uForm (unitaryInvolution F 2 f) a a = 0 → IsUTransGroup (unitaryInvolution F 2 f) a T →
        ∃ s : Finset K, s.card ≤ 2 * m - 3 ∧ (⨆ g ∈ s, conjSub (T.map Φ) g) = ⊤

theorem unitaryRootStatement_of_models (hD : SUModelDisjoint) (hM : SUModelMoves)
    (hC : SUModelCenter) (hK : SUModelCard) (hN : SUModelCount) (hG : SUModelGen) :
    UnitaryRootStatement := by
  intro K _ _ A hA
  obtain ⟨f, hf, Δ, hΔ, hAΔ⟩ := hA
  obtain ⟨m, Φ, a, T, hm, hΦ, hker, ha, haa, hT, rfl⟩ :=
    exists_isUTransGroup_of_transvConclusionSU hf hΔ hAΔ
  have hF := card_galoisField_two_mul hf
  refine ⟨classicalRootIrrStatement_holds K _ (Or.inr ⟨f, hf, Δ, hΔ, hAΔ⟩), ?_, ?_, ?_, ?_⟩
  · exact hD m _ f hF hm K Φ hΦ hker.le a T ha haa hT
  · exact hM m _ f hF hm K Φ hΦ hker.le a T ha haa hT
  · exact hC m _ f hF hm K Φ hΦ hker.le a T ha haa hT
  · obtain ⟨S, hS, hinj⟩ := hN m _ f hF hm K Φ hΦ hker.le a T ha haa hT
    obtain ⟨s, hs, hgen⟩ := hG m _ f hF hm K Φ hΦ hker.le a T ha haa hT
    have hq := hK m _ f hF hm K Φ hΦ hker.le a T ha haa hT
    refine ⟨2 * m - 3, S.card, by omega, ?_, ⟨s, hs, hgen⟩, ⟨S, rfl, hinj⟩⟩
    rw [hq]
    have h2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    calc 2 * (2 ^ f) ^ (2 * m - 3 - 1) ≤ 2 ^ f * (2 ^ f) ^ (2 * m - 3 - 1) :=
          Nat.mul_le_mul_right _ h2
      _ = (2 ^ f) ^ (2 * m - 3) := by
          rw [← pow_succ']; congr 1; omega
      _ ≤ S.card := hS

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection.ModelRank

theorem suModelDisjoint_holds : SUModelDisjoint := by
  intro m F _ _ _ f hF hm K _ Φ hΦ hker a T ha haa hT g hcent hne
  have hσ := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution F 2 f c = c → ∃ e, e + unitaryInvolution F 2 f e = c :=
    fun c hc => exists_add_unitaryInvolution_eq hF hc
  obtain ⟨d, hdd, had, -, G⟩ := exists_suFacts hF hm ha haa hT
  have hPerp : SUPerpStmt (unitaryInvolution F 2 f) m :=
    fun ha haa hvv hav hva => exists_isotropic_perp_not_perp hσ htr ha haa hvv hav hva
  have hnormK : ∀ {k : K}, k ∈ Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K) →
      ∃ g ∈ uLine (unitaryInvolution F 2 f) a, Φ g = k :=
    fun hk => exists_mem_uLine_of_mem_normalizer_map hF hPerp hΦ hker ha haa hT hk
  have hcore := pCoreOf_normalizer_map_eq hF hΦ hker ha haa hT hnormK
    (suCoreStatement_holds m F f hF hm a T ha haa hT)
  exact conjSub_inf_pCoreOf_eq_bot_su hσ hΦ hker hT haa hdd had G hcore hcent hne

theorem suModelMoves_holds : SUModelMoves := by
  intro m F _ _ _ f hF hm K _ Φ hΦ hker a T ha haa hT
  have hσ := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution F 2 f c = c → ∃ e, e + unitaryInvolution F 2 f e = c :=
    fun c hc => exists_add_unitaryInvolution_eq hF hc
  obtain ⟨d, hdd, had, -, G⟩ := exists_suFacts hF hm ha haa hT
  have hPerp : SUPerpStmt (unitaryInvolution F 2 f) m :=
    fun ha haa hvv hav hva => exists_isotropic_perp_not_perp hσ htr ha haa hvv hav hva
  have hnormK : ∀ {k : K}, k ∈ Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K) →
      ∃ g ∈ uLine (unitaryInvolution F 2 f) a, Φ g = k :=
    fun hk => exists_mem_uLine_of_mem_normalizer_map hF hPerp hΦ hker ha haa hT hk
  have hcore := pCoreOf_normalizer_map_eq hF hΦ hker ha haa hT hnormK
    (suCoreStatement_holds m F f hF hm a T ha haa hT)
  exact exists_conjSub_not_commute_su hσ htr hker hT haa hdd had G hcore

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped commutatorElement

theorem suModelCenter_holds : SUModelCenter := by
  intro m F _ _ _ f hF hm K _ Φ hΦ hker a T ha haa hT x hx hxc
  have hσ := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution F 2 f c = c → ∃ e, e + unitaryInvolution F 2 f e = c :=
    fun c hc => exists_add_unitaryInvolution_eq hF hc
  obtain ⟨d, hdd, had, Θ, G⟩ := exists_suFacts hF hm ha haa hT
  have hPerp : SUPerpStmt (unitaryInvolution F 2 f) m :=
    fun ha haa hvv hav hva => exists_isotropic_perp_not_perp hσ htr ha haa hvv hav hva
  have hnormK : ∀ {k : K}, k ∈ Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K) →
      ∃ g ∈ uLine (unitaryInvolution F 2 f) a, Φ g = k :=
    fun hk => exists_mem_uLine_of_mem_normalizer_map hF hPerp hΦ hker ha haa hT hk
  have hcore := pCoreOf_normalizer_map_eq hF hΦ hker ha haa hT hnormK
    (suCoreStatement_holds m F f hF hm a T ha haa hT)
  rw [hcore] at hx hxc
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map_of_mem Φ
    (mem_of_forall_commute_of_mem_uRad hσ htr haa hdd had Θ G hz fun u hu => ?_)
  have hk : ⁅z, u⁆ ∈ Φ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hxc (Φ u) (Subgroup.mem_map_of_mem Φ hu)
  exact commutatorElement_eq_one_iff_mul_comm.1
    (eq_one_of_mem_isUTransGroup_of_mem_center hσ haa hdd had hT (Θ.comm_mem hz hu) (hker hk))

theorem suModelCard_holds : SUModelCard := by
  intro m F _ _ _ f hF hm K _ Φ hΦ hker a T ha haa hT
  have hσ := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution F 2 f c = c → ∃ e, e + unitaryInvolution F 2 f e = c :=
    fun c hc => exists_add_unitaryInvolution_eq hF hc
  obtain ⟨d, hdd, had⟩ := exists_isotropic_partner hσ htr ha haa
  have hinj : Set.InjOn Φ (T : Set (SU (unitaryInvolution F 2 f) m)) := by
    intro x hx y hy hxy
    have h1 : x * y⁻¹ ∈ Φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    exact mul_inv_eq_one.1 (eq_one_of_mem_isUTransGroup_of_mem_center hσ haa hdd had hT
      (T.mul_mem hx (T.inv_mem hy)) (hker h1))
  have h2 := Nat.card_image_of_injOn hinj
  rw [← Subgroup.coe_map] at h2
  calc Nat.card ↥(T.map Φ) = Nat.card ↥((T.map Φ : Subgroup K) : Set K) := rfl
    _ = Nat.card ↥(T : Set (SU (unitaryInvolution F 2 f) m)) := h2
    _ = Nat.card ↥T := rfl
    _ = Nat.card (traceZero (unitaryInvolution F 2 f)) := ModelRank.IsUTransGroup.natCard_eq ha hT
    _ = 2 ^ f := CFSG.LieType.Steinberg.card_traceZero hF

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection.ModelRank

theorem suModelCount_holds : SUModelCount := by
  intro m F _ _ _ f hF hm K _ Φ hΦ hker a T ha haa hT
  have hσ := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution F 2 f c = c → ∃ e, e + unitaryInvolution F 2 f e = c :=
    fun c hc => exists_add_unitaryInvolution_eq hF hc
  obtain ⟨d, hdd, had⟩ := exists_isotropic_partner hσ htr ha haa
  obtain ⟨S, hS, hinj⟩ := exists_finset_injOn_conjSub_map hσ htr hker haa hdd had hT
  exact ⟨S, (natCard_isoPairs hF (by omega) haa hdd had).symm.le.trans hS, hinj⟩

end CFSG.RankThree.GF2n.Tim79a
