module

public import CFSG.Quasithin.Vol2.Ch11SecCBasic
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.E3Prop
public import CFSG.Quasithin.Vol2.Ch11SecABasic
public import CFSG.Quasithin.Vol2.Ch11StatementsE

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem oTwoUpper_oTwoUpper (H : Subgroup G) : oTwoUpper (oTwoUpper H) = oTwoUpper H := by
  refine le_antisymm (oTwoUpper_le _) ?_
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd hx.1 hx.2) hx.2

variable [Finite G]

theorem oTwoUpper_sup_eq {T H : Subgroup G} (hT : QuasithinUnique.IsSylowTwoOf T H) :
    oTwoUpper H ⊔ T = H :=
  le_antisymm (sup_le (oTwoUpper_le H) hT.1)
    (F7.isSylowTwoOf_le_sup_of_two_power hT (le_normalizer_oTwoUpper H)
      fun _ hx => exists_pow_mem_oTwoUpper H hx)

omit [Finite G] in
theorem pCore_eq_subgroupOf (K : Subgroup G) :
    CFSG.pCore 2 ↥K = (pCoreOf 2 K).subgroupOf K := by
  rw [pCoreOf, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]

variable {T L I : Subgroup G} {n : ℕ}

theorem oTwoUpper_data (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) {V₁ H : Subgroup G}
    (hyp : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (h31 : Hyp11_3_1 T L I n V₁ H)
    (hnot : ¬ Concl11_3_2 T L I n V₁ H) :
    quasithinIsCComponent (oTwoUpper H) H ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        Nonempty (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H) ≃*
          Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨k, hk, K, hKC, -, hiso, hKeq⟩ := h1135 G T L I n V₁ H hyp hV₁ h31 hnot
  have hkn : k = n := eq_of_nParam_eq hk (h1136 G T L I n V₁ H hyp hV₁ h31 hnot)
  subst hkn
  have hK : K = oTwoUpper H := hKeq fun h => absurd h (lt_irrefl k)
  subst hK
  exact ⟨hKC, hiso⟩

theorem pCoreOf_le_centralizer_VZ (hyp : Hyp11 G T L I n) {V₁ H : Subgroup G}
    (h31 : Hyp11_3_1 T L I n V₁ H) :
    pCoreOf 2 H ≤ Subgroup.centralizer (VZ T H : Set G) := by
  have hT := SecA.isSylowTwoOf_of_isHStar hyp h31.hstar
  have hCH := charTwo_of_inH hyp.fsu.qtke.2.1 (hyp.fsu.sylow.1.toSylow hyp.fsu.sylow.2)
    h31.hstar.1
  obtain ⟨hVH, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hCH le_rfl
  exact Subgroup.le_centralizer_iff.mp (hVH.trans inf_le_right)

theorem commutator_eq_bot_of_le_centralizer (hyp : Hyp11 G T L I n) {V₁ H : Subgroup G}
    (h31 : Hyp11_3_1 T L I n V₁ H)
    (hK : oTwoUpper H ≤ Subgroup.centralizer (VZ T H : Set G)) :
    ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  have hT := SecA.isSylowTwoOf_of_isHStar hyp h31.hstar
  refine (oTwoUpper_sup_eq hT).ge.trans
    (sup_le (hK.trans (Subgroup.centralizer_le (le_conjClosure _ H))) ?_)
  exact Subgroup.le_centralizer_iff.mp
    ((E3.omegaOneCenter_le_inf_centralizer T).trans inf_le_right)

theorem le_centralizer_of_sup {H W : Subgroup G}
    (hKW : oTwoUpper H ≤ Subgroup.normalizer (W : Set G))
    (h : ∀ x ∈ oTwoUpper H, ∃ c ∈ oTwoUpper H ⊓ Subgroup.centralizer (W : Set G),
      ∃ p ∈ pCoreOf 2 (oTwoUpper H), x = c * p) :
    oTwoUpper H ≤ Subgroup.centralizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H
  set C' := K ⊓ Subgroup.centralizer (W : Set G)
  suffices hKC : K ≤ C' from hKC.trans inf_le_right
  refine (oTwoUpper_oTwoUpper H).ge.trans (oTwoUpper_le_of_pow_mem fun x hx => ?_)
  obtain ⟨c, hc, p, hp, rfl⟩ := h x hx
  obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) ⟨p, hp⟩
  have hj' : p ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hpK : p ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hp
  have hpN : p ∈ Subgroup.normalizer (C' : Set G) := by
    have h1 := Subgroup.le_normalizer hpK
    have h2 := A1a.le_normalizer_centralizer hKW hpK
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro y
    simp only [C', Subgroup.mem_inf]
    rw [h1 y, h2 y]
  obtain ⟨c', hc', hpow⟩ := A4.exists_pow_mul_eq hc hpN (2 ^ j)
  exact ⟨j, by rw [hpow, hj', mul_one]; exact hc'⟩

theorem inf_centralizer_VZ_eq (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) {V₁ H : Subgroup G}
    (hyp : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (h31 : Hyp11_3_1 T L I n V₁ H)
    (hnot : ¬ Concl11_3_2 T L I n V₁ H) :
    oTwoUpper H ⊓ Subgroup.centralizer (VZ T H : Set G) = pCoreOf 2 (oTwoUpper H) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := oTwoUpper_data h1135 h1136 hyp hV₁ h31 hnot
  set K := oTwoUpper H with hKdef
  have hKH : K ≤ H := oTwoUpper_le H
  have hKV : K ≤ Subgroup.normalizer (VZ T H : Set G) :=
    hKH.trans (le_normalizer_conjClosure _ H)
  have hPK : pCoreOf 2 K ≤ pCoreOf 2 H :=
    F7.pCoreOf_mono_of_le_normalizer hKH (le_normalizer_oTwoUpper H)
  refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
    (hPK.trans (pCoreOf_le_centralizer_VZ hyp h31)))
  have hsimple := isSimpleGroup_SL2 (by have := hyp.one_lt; omega) hF
  set C := (autOnHom K (VZ T H) hKV).ker
  set P := CFSG.pCore 2 ↥K
  have hN : ((C.map (QuotientGroup.mk' P)).map e.toMonoidHom).Normal :=
    ((inferInstance : C.Normal).map _ (QuotientGroup.mk'_surjective P)).map _ e.surjective
  have hmemC : ∀ x : ↥K, x ∈ C ↔ (x : G) ∈ Subgroup.centralizer (VZ T H : Set G) := by
    intro x
    show x ∈ (autOnHom K (VZ T H) hKV).ker ↔ _
    rw [ker_autOnHom, Subgroup.mem_subgroupOf]
  rcases hN.eq_bot_or_eq_top with hbot | htop
  · rw [Subgroup.map_eq_bot_iff_of_injective _ e.injective, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk'] at hbot
    intro x hx
    have := hbot ((hmemC ⟨x, hx.1⟩).mpr hx.2)
    rw [show P = (pCoreOf 2 K).subgroupOf K from pCore_eq_subgroupOf K,
      Subgroup.mem_subgroupOf] at this
    exact this
  · exfalso
    apply h31.moves
    apply commutator_eq_bot_of_le_centralizer hyp h31
    refine le_centralizer_of_sup hKV fun x hx => ?_
    have hy : e (QuotientGroup.mk' P ⟨x, hx⟩) ∈ (C.map (QuotientGroup.mk' P)).map e.toMonoidHom :=
      htop ▸ Subgroup.mem_top _
    obtain ⟨y, ⟨c, hc, rfl⟩, hcy⟩ := Subgroup.mem_map.mp hy
    have hcx : QuotientGroup.mk' P c = QuotientGroup.mk' P ⟨x, hx⟩ := e.injective hcy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcx
    refine ⟨c, ⟨c.2, (hmemC c).mp hc⟩, ((c⁻¹ * ⟨x, hx⟩ : ↥K) : G), ?_, ?_⟩
    · rw [show P = (pCoreOf 2 K).subgroupOf K from pCore_eq_subgroupOf K,
        Subgroup.mem_subgroupOf] at hcx
      exact hcx
    · simp

theorem ker_autOnHom_VZ (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) {V₁ H : Subgroup G}
    (hyp : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (h31 : Hyp11_3_1 T L I n V₁ H)
    (hnot : ¬ Concl11_3_2 T L I n V₁ H)
    (hKV : oTwoUpper H ≤ Subgroup.normalizer (VZ T H : Set G)) :
    (autOnHom (oTwoUpper H) (VZ T H) hKV).ker = CFSG.pCore 2 ↥(oTwoUpper H) := by
  rw [ker_autOnHom, pCore_eq_subgroupOf, ← inf_centralizer_VZ_eq h1135 h1136 hyp hV₁ h31 hnot]
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem lemma11_3_7_one (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) {V₁ H : Subgroup G}
    (hyp : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (h31 : Hyp11_3_1 T L I n V₁ H)
    (hnot : ¬ Concl11_3_2 T L I n V₁ H) :
    quasithinIsCComponent (oTwoUpper H) H ∧
      Nonempty (↥(autOn (oTwoUpper H) (VZ T H)) ≃*
        ↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H)) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        Nonempty (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H) ≃*
          Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨hKC, hiso⟩ := oTwoUpper_data h1135 h1136 hyp hV₁ h31 hnot
  have hKV : oTwoUpper H ≤ Subgroup.normalizer (VZ T H : Set G) :=
    (oTwoUpper_le H).trans (le_normalizer_conjClosure _ H)
  refine ⟨hKC, ⟨(autOnEquiv _ _ hKV).trans (QuotientGroup.quotientMulEquivOfEq
    (ker_autOnHom_VZ h1135 h1136 hyp hV₁ h31 hnot hKV))⟩, hiso⟩

end CFSG.Quasithin.Vol2.Ch11.SecC
