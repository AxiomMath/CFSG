module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2PartTwoSzNat
public import CFSG.Quasithin.Recognition.Stroth.Str83G2PartTwoSzMin
public import CFSG.RankThree.GF2n.Tim81.Sec4.ConjRep
public import CFSG.Quasithin.Recognition.Stroth.Str83G2PartTwoSz2
public import CFSG.Quasithin.Recognition.Stroth.Str83G2SzModule2
public import CFSG.RankThree.GF2n.Tim81.Sec2.NaturalFixed
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzCor23

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.QuasithinUnique.Setup.X7 CFSG.LieType.Ree CFSG.LieType.BorelTits
open CFSG.Quasithin.H13 CFSG.Blueprint CFSG.RankThree.GF2n.Tim81.Sec2

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

structure Str83Z1MainData (L1 L2 S : Subgroup G) (a : ℕ) (K : Type) [Field K] [Finite K]
    where
  e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a K
  c : ℕ
  φ : Additive ↥(Z1 L1 L2 S) ≃+ (Fin 4 → K)
  map_S : (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a K
  nat : ∀ (h : ↥(L1 ⊔ S)) (z w : ↥(Z1 L1 L2 S)),
    (w : G) = (h : G) * z * (h : G)⁻¹ →
    φ (Additive.ofMul w) = Matrix.mulVec
      ((((e (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) h) : ↥(suzukiGroup a K)) :
        Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c))
      (φ (Additive.ofMul z))
  card : Nat.card ↥(Z1 L1 L2 S) = 2 ^ (4 * (2 * a + 1))
  irreducible : ∀ Y : Subgroup G, Y ≤ Z1 L1 L2 S →
    L1 ⊔ S ≤ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = Z1 L1 L2 S

theorem conjSubgroup_weyl_szZ {a : ℕ} {K : Type} [Field K] [Finite K] :
    CFSG.CGT.Timmesfeld75.conjSubgroup (suzukiWElt a K)
      (CFSG.RankThree.GF2n.Tim81.Sec2.szZ a K) = suzukiZ0 a K := by
  have h : CFSG.RankThree.GF2n.Tim81.Sec2.szZ a K =
      CFSG.CGT.Timmesfeld75.conjSubgroup (suzukiWElt a K) (suzukiZ0 a K) := rfl
  rw [h, CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup, suzukiWElt_mul_self,
    CFSG.CGT.Timmesfeld75.conjSubgroup_one]

structure Str83Z1FrameData (L1 L2 S : Subgroup G) (a : ℕ) (K : Type) [Field K] [Finite K]
    where
  e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a K
  X0 : Subgroup G
  mem_X0 : ∀ t : G, t ∈ X0 ↔ t ∈ S ∧ t ^ 2 ∈ Q1 L1 L2 S
  X0_le_S : X0 ≤ S
  Q1_le_X0 : Q1 L1 L2 S ≤ X0
  map_S : (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a K
  map_X0 : (szX0bar X0 L1 L2 S).map e.toMonoidHom = suzukiZ0 a K
  relIndex : (Z1 L1 L2 S ⊓ Subgroup.centralizer (X0 : Set G)).relIndex
    (Z1 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2

theorem nonempty_str83Z1FrameData
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nonempty (Str83Z1FrameData L1 L2 S a K) := by
  classical
  let eSz := Classical.choice hSz
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨eSz⟩⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hSyl1 : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hszU3 : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ (2 * a + 1)) :=
    Or.inl ⟨a, ha, rfl, ⟨(oTwoQuotCongr (MulEquiv.subgroupCongr hsup1)).trans
      ((oTwoQuotSupEquiv hF.1).trans eSz)⟩⟩
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hZ1ea : IsElemAbelian 2 (Z1 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)
  obtain ⟨X0, e, hX0mem, hX0S, hQ1X0, hU, hX0map⟩ :=
    exists_equiv_z1_sylow hK hF hB ha ⟨eSz⟩ hL2 hII hJ
  obtain ⟨X0', hX0'mem, hQ1X0', hX0'rel, -⟩ :=
    exists_X0 (q := 2 ^ (2 * a + 1)) hszU3 hSyl1
  have hX0'eq : X0' = X0 := by
    ext t
    rw [hX0'mem t, hX0mem t, hpCore1]
  have hX0'relQ : (Q1 L1 L2 S).relIndex X0' = 2 ^ (2 * a + 1) := by
    rw [← hpCore1]
    exact hX0'rel
  have hrelX0 : (Q1 L1 L2 S).relIndex X0 = 2 ^ (2 * a + 1) := by
    rw [← hX0'eq]
    exact hX0'relQ
  obtain ⟨E, X0'', hES, hEea, hEnotQ, hQ1X0'', hX0''S, hsupX0'', hX0''rel, hCX0'', hEq''⟩ :=
    str83_partTwo_generator_data hF hB ha ⟨eSz⟩ hL2 hII hJ
  have hQ1N : L1 ⊔ S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) := by
    rw [← hpCore1]
    exact le_normalizer_pCoreOf 2 (L1 ⊔ S)
  have hEN : E ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hES.trans ((le_sup_right : S ≤ L1 ⊔ S).trans hQ1N)
  have hX0''sq : ∀ t ∈ X0'', t ^ 2 ∈ Q1 L1 L2 S := by
    intro t ht
    rw [show X0'' = E ⊔ Q1 L1 L2 S from hsupX0''.symm, sup_comm] at ht
    obtain ⟨q, hq, e, he, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hEN).mp ht
    have hq' : e * q * e⁻¹ ∈ Q1 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hEN he) q).mp hq
    have he2 : e * e = 1 := by
      have h := hEea.2 e he
      rwa [pow_two] at h
    have hsq : (q * e) ^ 2 = q * (e * q * e⁻¹) := by
      rw [pow_two]
      calc q * e * (q * e) = q * (e * q * e⁻¹) * (e * e) := by group
        _ = q * (e * q * e⁻¹) := by rw [he2]; group
    rw [hsq]
    exact (Q1 L1 L2 S).mul_mem hq hq'
  have hX0''le : X0'' ≤ X0 := by
    intro t ht
    rw [hX0mem t]
    exact ⟨hX0''S ht, hX0''sq t ht⟩
  have hcard : Nat.card ↥X0'' = Nat.card ↥X0 := by
    have h1 := Subgroup.relIndex_mul_card (H := Q1 L1 L2 S) (K := X0'')
    have h2 := Subgroup.relIndex_mul_card (H := Q1 L1 L2 S) (K := X0)
    rw [inf_eq_left.mpr hQ1X0'', hX0''rel] at h1
    rw [inf_eq_left.mpr hQ1X0, hrelX0] at h2
    exact h1.symm.trans h2
  have hX0eq : X0'' = X0 :=
    Subgroup.eq_of_le_of_card_ge hX0''le (le_of_eq hcard.symm)
  have hrel : (Z1 L1 L2 S ⊓ Subgroup.centralizer (X0 : Set G)).relIndex
      (Z1 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [← hX0eq, hCX0'']
    exact hEq''
  exact ⟨Str83Z1FrameData.mk e X0 hX0mem hX0S hQ1X0 hU hX0map hrel⟩

end CFSG.Quasithin.Stroth

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.QuasithinUnique.Setup.X7 CFSG.LieType.Ree CFSG.LieType.BorelTits
open CFSG.Quasithin.H13 CFSG.Blueprint CFSG.RankThree.GF2n.Tim81.Sec2

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}


theorem str83_partTwo_z1_main
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nonempty (Str83Z1MainData L1 L2 S a K) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Fintype.card K = 2 ^ (2 * a + 1) := by
    rw [Fintype.card_eq_nat_card]; exact hK
  haveI : CharP K 2 := charP_of_card_eq_prime_pow hcardF
  let eSz := Classical.choice hSz
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨eSz⟩⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hC : S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) = Q1 L1 L2 S :=
    inf_centralizer_z1_eq_q1_of_caseII hF hB (Or.inl ⟨a, ha, ⟨eSz⟩⟩) hII
  have hZ1ea : IsElemAbelian 2 (Z1 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hZ1S : Z1 L1 L2 S ≤ S := (omegaOneCenterOf_le _).trans hQ1S
  have hHZ1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
    have hP1 : L1 ⊔ S ≤ P1 L1 L2 S :=
      sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
    exact hP1.trans ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S)))
  have hQ1C : Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    Q1_le_centralizer_Z1 L1 L2 S
  have hcent : Z1 L1 L2 S ⊓ Subgroup.centralizer ((L1 ⊔ S : Subgroup G) : Set G) = ⊥ :=
    str83_partTwo_centralizer_sup_z1_eq_bot hF hB ha ⟨eSz⟩ hL2 hZ2
  let D : Str83Z1FrameData L1 L2 S a K :=
    Classical.choice (nonempty_str83Z1FrameData hF hB ha ⟨eSz⟩ hL2 hII hJ hK)
  have hX0mem : ∀ t : G, t ∈ D.X0 ↔ t ∈ S ∧ t ^ 2 ∈ Q1 L1 L2 S := D.mem_X0
  have hX0S : D.X0 ≤ S := D.X0_le_S
  have hQ1X0 : Q1 L1 L2 S ≤ D.X0 := D.Q1_le_X0
  have hU : (szSbar L1 L2 S).map D.e.toMonoidHom = suzukiU a K := D.map_S
  have hrel := D.relIndex
  trace_state
  set H : Subgroup G := L1 ⊔ S with hHdef
  set W : Subgroup G := Z1 L1 L2 S with hWdef
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := by
    rw [hHdef, hWdef]; exact hHZ1
  have hQ1H : Q1 L1 L2 S ≤ H := by
    rw [hHdef]
    exact (le_sup_right : S ≤ L1 ⊔ S) |>.trans' hQ1S
  have hQ1W : Q1 L1 L2 S ≤ Subgroup.centralizer (W : Set G) := by
    rw [hWdef]; exact hQ1C
  have hcoreH : pCoreOf 2 H = Q1 L1 L2 S := by
    rw [hHdef]; exact hpCore1
  have hO : pCoreOf 2 H ≤ centralizerMod (⊥ : Subgroup G) H W := by
    intro x hx
    refine ⟨CFSG.openPCoreOf_le 2 H hx, ?_, ?_⟩
    · rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x
    · intro u hu
      have hcomm : u * x = x * u :=
        (Subgroup.mem_centralizer_iff.mp (hQ1W (hcoreH ▸ hx))) u hu
      have h1 : x * u * x⁻¹ * u⁻¹ = 1 := by
        rw [show x * u * x⁻¹ * u⁻¹ = (x * u) * (u * x)⁻¹ by group, hcomm, mul_inv_cancel]
      rw [h1]; exact Subgroup.one_mem ⊥
  have hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W) := by
    rw [hWdef]; exact isElemAbelian_chiefMod_bot hZ1ea
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let ρ := sectionRep (D14.le_normalizer_bot H) hHW (D14.le_normalizer_bot W) hE hO D.e
  have hcentW : W ⊓ Subgroup.centralizer (H : Set G) = ⊥ := by
    rw [hWdef, hHdef]; exact hcent
  have hcentρ : fixedSub ρ ⊤ = ⊥ := by
    change CFSG.RankThree.FFModules.fixSub ρ ⊤ = ⊥
    rw [eq_bot_iff]
    intro x hx
    set w : ↥W := (chiefModBotMulEquiv W).symm x.toMul with hw
    have hxw : Additive.ofMul (chiefModBotMulEquiv W w) = x := by
      apply Additive.ext
      rw [show (Additive.ofMul (chiefModBotMulEquiv W w)).toMul =
        chiefModBotMulEquiv W w from rfl, hw, MulEquiv.apply_symm_apply]
    rw [← hxw] at hx
    have htopmap : ((⊤ : Subgroup ↥H).map
        (QuotientGroup.mk' (pCore 2 ↥H))).map D.e.toMonoidHom = ⊤ := by
      rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
        Subgroup.map_top_of_surjective _ D.e.surjective]
    have hsubtop : (⊤ : Subgroup ↥H).map H.subtype = H := by
      simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup G) H
    have hiff := (mem_fixSub_sectionRep_bot_iff (H := H) (W := W) (D14.le_normalizer_bot H)
      hHW hE hO D.e (⊤ : Subgroup ↥H) w)
    rw [htopmap, hsubtop] at hiff
    have hwC : (w : G) ∈ Subgroup.centralizer (H : Set G) := hiff.1 hx
    have hwbot : w = 1 := by
      have hmem : (w : G) ∈ W ⊓ Subgroup.centralizer (H : Set G) :=
        Subgroup.mem_inf.mpr ⟨w.2, hwC⟩
      rw [hcentW] at hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    rw [← hxw, hwbot, map_one]
    rfl
  have hX0H : D.X0 ≤ H := hX0S.trans (le_sup_right : S ≤ L1 ⊔ S)
  have hfixcard : Nat.card (fixedSub ρ (suzukiZ0 a K)) = Nat.card ↥(W ⊓
      Subgroup.centralizer (D.X0 : Set G)) := by
    have hmap1 : (D.X0.subgroupOf H).map H.subtype = D.X0 :=
      Subgroup.map_subgroupOf_eq_of_le hX0H
    have h := card_fixSub_sectionRep_bot (H := H) (W := W) (D14.le_normalizer_bot H)
      hHW hE hO D.e (D.X0.subgroupOf H)
    rw [hmap1] at h
    have hmap3 : ((D.X0.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))).map
        D.e.toMonoidHom = suzukiZ0 a K := by
      rw [show (D.X0.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H)) =
        szX0bar D.X0 L1 L2 S from rfl]
      change (szX0bar D.X0 L1 L2 S).map D.e.toMonoidHom = suzukiZ0 a K
      exact D.map_X0
    rw [hmap3] at h
    exact h
  have hMcard : Nat.card (Additive (Ch3z.chiefMod ⊥ W)) =
      (2 ^ (2 * a + 1)) ^ 2 * Nat.card (fixedSub ρ (suzukiZ0 a K)) := by
    have hWcard : Nat.card ↥W = (2 ^ (2 * a + 1)) ^ 2 *
        Nat.card ↥(W ⊓ Subgroup.centralizer (D.X0 : Set G)) := by
      have h := Subgroup.relIndex_mul_card (H := W ⊓ Subgroup.centralizer (D.X0 : Set G))
        (K := W)
      rw [inf_right_comm] at h
      have hrel' : (W ⊓ Subgroup.centralizer (D.X0 : Set G)).relIndex W =
          (2 ^ (2 * a + 1)) ^ 2 := by
        rw [hWdef]; exact hrel
      rw [hrel', inf_idem] at h
      exact h.symm
    rw [hfixcard]
    have hcard : Nat.card (Additive (Ch3z.chiefMod ⊥ W)) = Nat.card ↥W :=
      Nat.card_congr (chiefModBotMulEquiv W).toEquiv.symm
    rw [hcard]
    exact hWcard
  have hWne : W ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥W = 1 := by rw [hbot]; exact Subgroup.card_bot
    have hM : Nat.card (Additive (Ch3z.chiefMod ⊥ W)) = Nat.card ↥W :=
      Nat.card_congr (chiefModBotMulEquiv W).toEquiv.symm
    rw [hM, h1] at hMcard
    have hq : 1 < (2 ^ (2 * a + 1)) ^ 2 := by
      have h2 : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
      nlinarith
    have hpos : 0 < Nat.card (fixedSub ρ (suzukiZ0 a K)) := Nat.card_pos
    nlinarith
  obtain ⟨Y, hYW, hYne, hYN, hYmin⟩ :=
    CFSG.RankThree.GF2n.Tim81.exists_minimal_normalized_le (H := H) (E := W) hWne hHW
  let Nsub : Subrepresentation ρ :=
    { toSubmodule := subZ (W := W) hE Y
      apply_mem_toSubmodule := fun g x hx =>
        sectionRep_mem_subZ (H := H) (W := W) hHW hO D.e hYN g hx }
  have hNsub_card : Nat.card (subZ (W := W) hE Y) = Nat.card ↥Y := natCard_subZ hYW
  have hNnl : Nontrivial Nsub.toSubmodule := by
    rw [Submodule.nontrivial_iff_ne_bot]
    intro hbot
    have h1 : Nat.card ↥Nsub.toSubmodule = 1 := by
      rw [hbot]
      simp
    have h2 : Nat.card ↥Y = 1 := by rw [← hNsub_card]; exact h1
    exact hYne ((Subgroup.card_eq_one).mp h2)

  have hNirr : Nsub.toRepresentation.IsIrreducible := by
    rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
    refine ⟨hNnl, ?_⟩
    intro U hU
    let Uamb : ChiefSubmodule (W := W) hE := U.map Nsub.toSubmodule.subtype
    let E : Subgroup G := subZPre (W := W) hE hZ1ea Uamb
    have hUamb_le : Uamb ≤ subZ (W := W) hE Y := by
      rintro x ⟨u, hu, rfl⟩
      exact u.2
    have hE_le_Y : E ≤ Y := by
      calc E = subZPre (W := W) hE hZ1ea Uamb := rfl
        _ ≤ subZPre (W := W) hE hZ1ea (subZ (W := W) hE Y) :=
            subZPre_mono hZ1ea hUamb_le
        _ = Y := subZPre_subZ hZ1ea hYW
    have hUamb_inv : ∀ (g : ↥(suzukiGroup a K))
        (x : Additive (Ch3z.chiefMod ⊥ W)), x ∈ Uamb →
        sectionRep (D14.le_normalizer_bot H) hHW (D14.le_normalizer_bot W) hE hO D.e g x ∈
          Uamb := by
      intro g x hx
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
      exact Submodule.mem_map.mpr ⟨Nsub.toRepresentation g u, hU g u hu, rfl⟩
    have hE_norm : H ≤ Subgroup.normalizer (E : Set G) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact sectionRep_subZPre_mem (H := H) (W := W) hHW hO D.e hZ1ea hUamb_inv hh hx
      · intro hx
        have hx' : h⁻¹ * (h * x * h⁻¹) * (h⁻¹)⁻¹ ∈ E :=
          sectionRep_subZPre_mem (H := H) (W := W) hHW hO D.e hZ1ea hUamb_inv
            (H.inv_mem hh) hx
        convert hx' using 2
        group
    by_cases hEbot : E = ⊥
    · left
      have hUamb_bot : Uamb = ⊥ := by
        rw [← subZ_subZPre (W := W) hZ1ea Uamb]
        change subZ (W := W) hE E = ⊥
        rw [hEbot, subZ_bot]
      have hmap : U.map Nsub.toSubmodule.subtype = ⊥ := by
        exact hUamb_bot
      exact Submodule.map_injective_of_injective Nsub.toSubmodule.subtype_injective
        (hmap.trans (Submodule.map_bot Nsub.toSubmodule.subtype).symm)
    · right
      have hEY : E = Y := hYmin E hE_le_Y hEbot hE_norm
      have hUamb_top : Uamb = Nsub.toSubmodule := by
        rw [← subZ_subZPre (W := W) hZ1ea Uamb]
        change subZ (W := W) hE E = Nsub.toSubmodule
        rw [hEY]
      have htop : (⊤ : Submodule (ZMod 2) Nsub.toSubmodule).map Nsub.toSubmodule.subtype =
          Nsub.toSubmodule := by
        rw [Submodule.map_top, Submodule.range_subtype]
      exact Submodule.map_injective_of_injective Nsub.toSubmodule.subtype_injective
        (hUamb_top.trans htop.symm)

  have hnt : ∃ g : ↥(suzukiGroup a K), Nsub.toRepresentation g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : Nsub.toSubmodule ≤ fixedSub ρ ⊤ := by
      intro x hx
      rw [mem_fixedSub]
      intro g _
      have h1 := congrArg
        (fun f : Module.End (ZMod 2) Nsub.toSubmodule => f ⟨x, hx⟩) (hcon g)
      rw [Module.End.one_apply] at h1
      exact (Subrepresentation.toRepresentation_apply_coe).mp h1
    have hbot : Nsub.toSubmodule = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' := hle hx
      rw [hcentρ] at hx'
      simpa using hx'
    have h1 : Nat.card ↥Y = 1 := by
      have h2 : Nat.card ↥Nsub.toSubmodule = 1 := by rw [hbot]; simp
      rw [← hNsub_card]; exact h2
    exact hYne ((Subgroup.card_eq_one).mp h1)
  have hbound : Nat.card ↥Nsub.toSubmodule ≤
      (2 ^ (2 * a + 1)) ^ 2 *
        Nat.card (fixedSub Nsub.toRepresentation (suzukiZ0 a K)) := by
    change Nat.card ↥Nsub.toSubmodule ≤ (2 ^ (2 * a + 1)) ^ 2 *
      Nat.card (CFSG.RankThree.FFModules.fixSub Nsub.toRepresentation (suzukiZ0 a K))
    let C : Submodule (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) :=
      CFSG.RankThree.FFModules.fixSub ρ (suzukiZ0 a K)
    have hCpos : 0 < Nat.card ↥C := Nat.card_pos
    have hcard := CFSG.RankThree.FFModules.card_inf_mul_card_sup Nsub.toSubmodule C
    have hsup_le : Nat.card ↥(Nsub.toSubmodule ⊔ C) ≤
        Nat.card (Additive (Ch3z.chiefMod ⊥ W)) :=
      Nat.card_le_card_of_injective (Submodule.subtype _) (Submodule.subtype_injective _)
    have h1 : Nat.card ↥Nsub.toSubmodule * Nat.card ↥C ≤
        Nat.card ↥(Nsub.toSubmodule ⊓ C) *
          Nat.card (Additive (Ch3z.chiefMod ⊥ W)) := by
      rw [← hcard]
      exact Nat.mul_le_mul_left _ hsup_le
    have hMcard' : Nat.card (Additive (Ch3z.chiefMod ⊥ W)) =
        (2 ^ (2 * a + 1)) ^ 2 * Nat.card ↥C := by
      exact hMcard
    have h2 : Nat.card ↥Nsub.toSubmodule * Nat.card ↥C ≤
        ((2 ^ (2 * a + 1)) ^ 2 * Nat.card ↥(Nsub.toSubmodule ⊓ C)) * Nat.card ↥C := by
      calc Nat.card ↥Nsub.toSubmodule * Nat.card ↥C
          ≤ Nat.card ↥(Nsub.toSubmodule ⊓ C) *
              Nat.card (Additive (Ch3z.chiefMod ⊥ W)) := h1
        _ = Nat.card ↥(Nsub.toSubmodule ⊓ C) *
              ((2 ^ (2 * a + 1)) ^ 2 * Nat.card ↥C) := by rw [hMcard']
        _ = ((2 ^ (2 * a + 1)) ^ 2 * Nat.card ↥(Nsub.toSubmodule ⊓ C)) *
              Nat.card ↥C := by ring
    have h3 := Nat.le_of_mul_le_mul_right h2 hCpos
    have h4 : Nat.card ↥(Nsub.toSubmodule ⊓ C) =
        Nat.card (CFSG.RankThree.FFModules.fixSub Nsub.toRepresentation (suzukiZ0 a K)) := by
      rw [natCard_fixedSub_toRepresentation (X := ↥(suzukiGroup a K))
        (W := Additive (Ch3z.chiefMod ⊥ W)) ρ Nsub (suzukiZ0 a K)]
      rw [inf_comm]
    rw [h4] at h3
    exact h3
  have hNnat : IsSzNatural Nsub.toRepresentation := by
    haveI : Fact Nsub.toRepresentation.IsIrreducible := ⟨hNirr⟩
    rcases isSzNatural_or_le_card (K := K) (a := a) hK Nsub.toRepresentation hnt with hnat | hbig
    · exact hnat
    · have hq16 : (2 ^ (2 * a + 1)) ^ 16 ≤ Nat.card ↥Nsub.toSubmodule := by
        rwa [show (2 ^ (2 * a + 1)) ^ 16 = 2 ^ (16 * (2 * a + 1)) by
          rw [← pow_mul]; ring_nf]
      have hq8lt : (2 ^ (2 * a + 1)) ^ 8 < Nat.card ↥Nsub.toSubmodule ^ 3 := by
        have hqpos : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
        have hq : (2 ^ (2 * a + 1)) ^ 8 < (2 ^ (2 * a + 1)) ^ 16 :=
          Nat.pow_lt_pow_right hqpos (by omega)
        calc (2 ^ (2 * a + 1)) ^ 8 < (2 ^ (2 * a + 1)) ^ 16 := hq
          _ ≤ Nat.card ↥Nsub.toSubmodule := hq16
          _ = Nat.card ↥Nsub.toSubmodule ^ 1 := (pow_one _).symm
          _ ≤ Nat.card ↥Nsub.toSubmodule ^ 3 :=
              Nat.pow_le_pow_right (Nat.card_pos) (by omega)
      have hN4 : Nat.card ↥Nsub.toSubmodule * (2 ^ (2 * a + 1)) ^ 8 <
          Nat.card ↥Nsub.toSubmodule ^ 4 := by
        have h := Nat.mul_lt_mul_of_pos_left hq8lt (Nat.card_pos (α := ↥Nsub.toSubmodule))
        rwa [show Nat.card ↥Nsub.toSubmodule * Nat.card ↥Nsub.toSubmodule ^ 3 =
          Nat.card ↥Nsub.toSubmodule ^ 4 by ring] at h
      have hN4le : Nat.card ↥Nsub.toSubmodule ^ 4 ≤
          (2 ^ (2 * a + 1)) ^ 8 *
            Nat.card (fixedSub Nsub.toRepresentation (suzukiZ0 a K)) ^ 4 := by
        calc Nat.card ↥Nsub.toSubmodule ^ 4
            ≤ ((2 ^ (2 * a + 1)) ^ 2 *
                Nat.card (fixedSub Nsub.toRepresentation (suzukiZ0 a K))) ^ 4 :=
              Nat.pow_le_pow_left hbound 4
          _ = (2 ^ (2 * a + 1)) ^ 8 *
                Nat.card (fixedSub Nsub.toRepresentation (suzukiZ0 a K)) ^ 4 := by ring
      have hlt0 : Nat.card ↥Nsub.toSubmodule * (2 ^ (2 * a + 1)) ^ 8 <
          (2 ^ (2 * a + 1)) ^ 8 *
            Nat.card (fixedSub Nsub.toRepresentation (suzukiZ0 a K)) ^ 4 :=
        lt_of_lt_of_le hN4 hN4le
      have hlt0' : (2 ^ (2 * a + 1)) ^ 8 * Nat.card ↥Nsub.toSubmodule <
          (2 ^ (2 * a + 1)) ^ 8 *
            Nat.card (fixedSub Nsub.toRepresentation (suzukiZ0 a K)) ^ 4 := by
        rwa [mul_comm (Nat.card ↥Nsub.toSubmodule) ((2 ^ (2 * a + 1)) ^ 8)] at hlt0
      have hlt : Nat.card ↥Nsub.toSubmodule <
          Nat.card (fixedSub Nsub.toRepresentation (suzukiZ0 a K)) ^ 4 :=
        lt_of_mul_lt_mul_left' hlt0' 
      refine isSzNatural_of_card_lt_fixedSub_conj (K := K) (a := a) hK
        Nsub.toRepresentation hnt (suzukiWElt a K) ?_
      rwa [conjSubgroup_weyl_szZ]

  have hYminZ : ∀ Y' : Subgroup G, Y' ≤ Y →
      L1 ⊔ S ≤ Subgroup.normalizer (Y' : Set G) → Y' = ⊥ ∨ Y' = Y := by
    intro Y' hle hN
    rw [← hHdef] at hN
    by_cases hbot : Y' = ⊥
    · exact Or.inl hbot
    · exact Or.inr (hYmin Y' hle hbot hN)
  have hQ : ∀ g m, ρ g m - m ∈ Nsub.toSubmodule := by
    intro g m
    refine sectionRep_sub_mem_subZ (H := H) (W := W) hHW hO D.e ?_ g m
    intro h hh z hz
    have hhS : h ∈ L1 ⊔ S := by rwa [hHdef] at hh
    have hzZ : z ∈ Z1 L1 L2 S := by rwa [hWdef] at hz
    exact str83_partTwo_comm_mem_minimal (L1 := L1) (L2 := L2) (S := S) (a := a)
      hF hB ha ⟨eSz⟩ hL2 hII hZ2 hJ (by rw [← hWdef]; exact hYW) hYne
      (by rw [← hHdef]; exact hYN) hYminZ hhS hzZ
  have hNat : fixedSub ρ (suzukiZ0 a K) ≤ Nsub.toSubmodule :=
    lemmaNat_sz (a := a) (K := K) ha hK ρ Nsub hNnat hQ hcentρ
  have hNfix : Nat.card (fixedSub Nsub.toRepresentation (suzukiZ0 a K)) =
      (2 ^ (2 * a + 1)) ^ 2 := by
    have h := natCard_fixedSub_conj_szZ (K := K) (a := a) hK Nsub.toRepresentation
      hNnat (suzukiWElt a K)
    rwa [conjSubgroup_weyl_szZ, hK] at h
  have hCMeq : Nat.card (fixedSub Nsub.toRepresentation (suzukiZ0 a K)) =
      Nat.card (fixedSub ρ (suzukiZ0 a K)) := by
    change Nat.card (CFSG.RankThree.FFModules.fixSub Nsub.toRepresentation (suzukiZ0 a K)) =
      Nat.card (CFSG.RankThree.FFModules.fixSub ρ (suzukiZ0 a K))
    rw [natCard_fixedSub_toRepresentation (X := ↥(suzukiGroup a K))
      (W := Additive (Ch3z.chiefMod ⊥ W)) ρ Nsub (suzukiZ0 a K)]
    have h : CFSG.RankThree.FFModules.fixSub ρ (suzukiZ0 a K) ⊓ Nsub.toSubmodule =
        CFSG.RankThree.FFModules.fixSub ρ (suzukiZ0 a K) := inf_eq_left.mpr hNat
    rw [h]
  have hNcard : Nat.card ↥Nsub.toSubmodule = (2 ^ (2 * a + 1)) ^ 4 := by
    obtain ⟨c, φ, -⟩ := hNnat
    have hK4 : Nat.card (Fin 4 → K) = (2 ^ (2 * a + 1)) ^ 4 := by
      rw [Nat.card_pi]
      simp [hcardF]
    change Nat.card (Additive ↥Nsub.toSubmodule) = (2 ^ (2 * a + 1)) ^ 4
    exact (Nat.card_congr φ.toEquiv).trans hK4
  have hNtop : Nsub = ⊤ := by
    have hcardM : Nat.card ↥Nsub.toSubmodule =
        Nat.card (Additive (Ch3z.chiefMod ⊥ W)) := by
      rw [hNcard, hMcard, ← hCMeq, hNfix]
      ring
    apply Subrepresentation.toSubmodule_injective
    change Nsub.toSubmodule = ⊤
    rw [Submodule.eq_top_iff_finrank_eq]
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Nsub.toSubmodule)
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive (Ch3z.chiefMod ⊥ W))
    rw [h1, h2] at hcardM
    exact Nat.pow_right_injective (by norm_num) hcardM

  have hρnat : IsSzNatural ρ := by
    obtain ⟨c, φ, hφ⟩ := hNnat
    have hsurj : Function.Surjective Nsub.toSubmodule.subtype := by
      intro x
      exact ⟨⟨x, by rw [hNtop]; exact Submodule.mem_top⟩, rfl⟩
    let e : ↥Nsub.toSubmodule ≃ₗ[ZMod 2] Additive (Ch3z.chiefMod ⊥ W) :=
      LinearEquiv.ofBijective Nsub.toSubmodule.subtype
        ⟨Nsub.toSubmodule.subtype_injective, hsurj⟩
    refine ⟨c, (e.symm.toAddEquiv).trans φ, ?_⟩
    intro g w
    let u : ↥Nsub.toSubmodule := e.symm w
    have h := hφ g u
    have he : (e.symm.toAddEquiv) (ρ g w) = Nsub.toRepresentation g u := by
      change e.symm (ρ g w) = Nsub.toRepresentation g u
      rw [LinearEquiv.symm_apply_eq]
      change ρ g w = ρ g (e u)
      rw [show e u = w from by
        change e (e.symm w) = w
        rw [LinearEquiv.apply_symm_apply]]
    simpa [AddEquiv.trans_apply, he] using h
  have hρfix : Nat.card (fixedSub ρ (suzukiZ0 a K)) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [← hCMeq, hNfix]
  have hM4 : Nat.card (Additive (Ch3z.chiefMod ⊥ W)) = (2 ^ (2 * a + 1)) ^ 4 := by
    rw [hMcard, hρfix]
    ring
  have hWcard : Nat.card ↥W = 2 ^ (4 * (2 * a + 1)) := by
    have h : Nat.card (Additive (Ch3z.chiefMod ⊥ W)) = Nat.card ↥W :=
      Nat.card_congr (chiefModBotMulEquiv W).toEquiv.symm
    rw [← h, hM4]
    rw [show (2 ^ (2 * a + 1)) ^ 4 = 2 ^ (4 * (2 * a + 1)) by
      rw [← pow_mul]; ring]

  obtain ⟨c, φ, hφ⟩ := hρnat
  have hnatural : ∃ (c : ℕ) (φ' : Additive ↥(Z1 L1 L2 S) ≃+ (Fin 4 → K)),
      ∀ (h : ↥(L1 ⊔ S)) (z w : ↥(Z1 L1 L2 S)),
        (w : G) = (h : G) * z * (h : G)⁻¹ →
        φ' (Additive.ofMul w) = Matrix.mulVec
          ((((D.e (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) h) : ↥(suzukiGroup a K)) :
            Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c))
          (φ' (Additive.ofMul z)) := by
    refine ⟨c, (chiefModBotMulEquiv W).toAdditive.trans φ, ?_⟩
    intro h z w hw
    have hstep := hφ (D.e (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) h))
      (Additive.ofMul (chiefModBotMulEquiv W z))
    have hact : ρ (D.e (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) h))
        (Additive.ofMul (chiefModBotMulEquiv W z)) =
        Additive.ofMul (chiefModBotMulEquiv W w) := by
      rw [show D.e (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) h) =
        D.e (QuotientGroup.mk h) from rfl]
      rw [sectionRep_apply]
      have hact' : sectionAction (D14.le_normalizer_bot H) hHW hE h
          (chiefModBotMulEquiv W z) =
          chiefModBotMulEquiv W
            ⟨(h : G) * (z : G) * (h : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp (hHW h.2) (z : G)).mp z.2⟩ := by
        exact
          sectionAction_bot_apply (H := H) (W := W) (D14.le_normalizer_bot H) hHW hE h z
      rw [hact']
      rw [show (⟨(h : G) * (z : G) * (h : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hHW h.2) (z : G)).mp z.2⟩ : ↥W) = w from
        Subtype.ext hw.symm]
    rw [hact] at hstep
    simpa using hstep

  have hρirr : ρ.IsIrreducible := by
    have htopirr : (⊤ : Subrepresentation ρ).toRepresentation.IsIrreducible := by
      rw [← hNtop]
      exact hNirr
    have hatom : IsAtom (⊤ : Subrepresentation ρ) :=
      (Subrepresentation.irreducible_iff_isAtom (⊤ : Subrepresentation ρ)).mp htopirr
    rw [Representation.IsIrreducible, isSimpleOrder_iff_isAtom_top]
    exact hatom
  have hirrZ : ∀ Y : Subgroup G, Y ≤ W → H ≤ Subgroup.normalizer (Y : Set G) →
      Y = ⊥ ∨ Y = W := by
    intro Y hYW hYN
    let U : Subrepresentation ρ :=
      { toSubmodule := subZ (W := W) hE Y
        apply_mem_toSubmodule := fun g x hx =>
          sectionRep_mem_subZ (H := H) (W := W) hHW hO D.e hYN g hx }
    rcases hρirr.eq_bot_or_eq_top U with h | h
    · left
      have hbot : subZ (W := W) hE Y = ⊥ := by
        have h' := congrArg Subrepresentation.toSubmodule h
        change U.toSubmodule = (⊥ : Subrepresentation ρ).toSubmodule
        exact h'
      have hsub : subZ (W := W) hE Y = subZ (W := W) hE (⊥ : Subgroup G) := by
        rw [hbot, subZ_bot]
      exact (subZ_inj hYW bot_le).1 hsub
    · right
      have htop : subZ (W := W) hE Y = ⊤ := by
        have h' := congrArg Subrepresentation.toSubmodule h
        change U.toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule
        exact h'
      have hsub : subZ (W := W) hE Y = subZ (W := W) hE W := by
        rw [htop, subZ_top]
      exact (subZ_inj hYW (le_refl W)).1 hsub

  obtain ⟨cNat, φNat, hφNat⟩ := hnatural
  refine ⟨Str83Z1MainData.mk D.e cNat φNat D.map_S hφNat ?_ ?_⟩
  · simpa [hWdef] using hWcard
  · intro Y hY hN
    rw [← hWdef] at hY
    rw [← hHdef] at hN
    rw [← hWdef]
    exact hirrZ Y hY hN

end CFSG.Quasithin.Stroth

end
