module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaNatZ1
public import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverUni
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Background.F7TwoInvAutWrap
public import CFSG.Quasithin.Background.SmithB45U3Nat
public import CFSG.Quasithin.H13.KG14726Elim
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaEquality

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem str86_atom_action_perfect {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    {N : Subgroup G} (h1 : Str86AtomIn (L1 ⊔ S) (Z1 L1 L2 S) N)
    (hNabel : IsElemAbelian 2 N) :
    Group.IsPerfect ↥(autOn (L1 ⊔ S) N) := by
  classical
  let H : Subgroup G := L1 ⊔ S
  letI : CommGroup ↥N := commGroupOfElemAbelian hNabel
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn h1.1
  let φ : ↥H →* MulAut ↥N := (conjAct N).comp (Subgroup.inclusion hHN)
  have hφrange : φ.range = autOn H N := by
    rw [show φ = (conjAct N).comp (Subgroup.inclusion hHN) from rfl, MonoidHom.range_comp,
      Subgroup.inclusion_range]
    rfl
  have hpCoreH : pCoreOf 2 H = Q1 L1 L2 S := str86_pCoreOf_sup_s_eq_q1 hF hSB hk hFc hU3
  have hQ1N : Q1 L1 L2 S ≤ Subgroup.centralizer (N : Set G) :=
    Subgroup.le_centralizer_iff.mpr (h1.1.1.trans (Z1_le_centralizer_Q1 L1 L2 S))
  have hker : pCore 2 ↥H ≤ φ.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    have hqQ1 : (q : G) ∈ Q1 L1 L2 S := by
      have := (F1.mem_pCore_iff_coe (H := H) q).mp hq
      rwa [hpCoreH] at this
    have hqC : (q : G) ∈ Subgroup.centralizer (N : Set G) := hQ1N hqQ1
    ext n
    have hcoe : (((conjAct N) (Subgroup.inclusion hHN q)) n : G) = (q : G) * (n : G) * (q : G)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe N (Subgroup.inclusion hHN q) n
    have hcomm : (n : G) * (q : G) = (q : G) * (n : G) :=
      Subgroup.mem_centralizer_iff.mp hqC n n.2
    change (((conjAct N) (Subgroup.inclusion hHN q)) n : G) = (n : G)
    rw [hcoe, ← hcomm]
    group
  let ψ : oTwoQuot ↥H →* MulAut ↥N := QuotientGroup.lift (pCore 2 ↥H) φ hker
  have hψapply : ∀ h : ↥H, ψ (QuotientGroup.mk' (pCore 2 ↥H) h) = φ h :=
    fun h => QuotientGroup.lift_mk' (pCore 2 ↥H) hker h
  have hψrange : ψ.range = autOn H N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥H) y
      rw [← hφrange, hψapply h]
      exact ⟨h, rfl⟩
    · intro hx
      rw [← hφrange] at hx
      obtain ⟨h, hh⟩ := hx
      exact ⟨QuotientGroup.mk' (pCore 2 ↥H) h, by rw [hψapply h]; exact hh⟩
  have hVU3 : VU3Big L1 := str86_vU3Big_of_stated hk hFc hU3
  have hqL1 : CFSG.IsQuasisimple (oTwoQuot ↥L1) := isQuasisimple_oTwoQuot_of_u3 hk hFc hU3
  have hqH : CFSG.IsQuasisimple (oTwoQuot ↥H) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (u3QEquiv hF hSB hVU3).symm hqL1
  haveI : Group.IsPerfect (oTwoQuot ↥H) := hqH.1
  have hperfRange : Group.IsPerfect ↥(ψ.range) := Group.IsPerfect.range ψ
  rwa [hψrange] at hperfRange


private noncomputable def str86ConjHom (H N : Subgroup G)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) : ↥H →* MulAut ↥N :=
  (conjAct N).comp (Subgroup.inclusion hHN)

private theorem str86ConjHom_range (H N : Subgroup G)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    (str86ConjHom H N hHN).range = autOn H N := by
  rw [str86ConjHom, MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

theorem str86_atom_center_quotient {L1 L2 S : Subgroup G}
    {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hC : Z1 L1 L2 S ⊓ Subgroup.centralizer ((L1 ⊔ S : Subgroup G) : Set G) = ⊥)
    {N : Subgroup G} (h1 : Str86AtomIn (L1 ⊔ S) (Z1 L1 L2 S) N)
    (hNabel : IsElemAbelian 2 N) :
    Nonempty (↥(autOn (L1 ⊔ S) N) ⧸ Subgroup.center ↥(autOn (L1 ⊔ S) N) ≃*
      StatedProj (StatedSU 3 (2 ^ k) F)) := by
  classical
  let H : Subgroup G := L1 ⊔ S
  letI : CommGroup ↥N := commGroupOfElemAbelian hNabel
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn h1.1
  let φ : ↥H →* MulAut ↥N := str86ConjHom H N hHN
  have hφrange : φ.range = autOn H N := str86ConjHom_range H N hHN
  have hpCoreH : pCoreOf 2 H = Q1 L1 L2 S := str86_pCoreOf_sup_s_eq_q1 hF hSB hk hFc hU3
  have hQ1N : Q1 L1 L2 S ≤ Subgroup.centralizer (N : Set G) :=
    Subgroup.le_centralizer_iff.mpr (h1.1.1.trans (Z1_le_centralizer_Q1 L1 L2 S))
  have hker : pCore 2 ↥H ≤ φ.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    have hqQ1 : (q : G) ∈ Q1 L1 L2 S := by
      have := (F1.mem_pCore_iff_coe (H := H) q).mp hq
      rwa [hpCoreH] at this
    have hqC : (q : G) ∈ Subgroup.centralizer (N : Set G) := hQ1N hqQ1
    ext n
    have hcoe : (((conjAct N) (Subgroup.inclusion hHN q)) n : G) = (q : G) * (n : G) * (q : G)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe N (Subgroup.inclusion hHN q) n
    have hcomm : (n : G) * (q : G) = (q : G) * (n : G) :=
      Subgroup.mem_centralizer_iff.mp hqC n n.2
    change (((conjAct N) (Subgroup.inclusion hHN q)) n : G) = (n : G)
    rw [hcoe, ← hcomm]
    group
  let ψ : oTwoQuot ↥H →* MulAut ↥N := QuotientGroup.lift (pCore 2 ↥H) φ hker
  have hψapply : ∀ h : ↥H, ψ (QuotientGroup.mk' (pCore 2 ↥H) h) = φ h :=
    fun h => QuotientGroup.lift_mk' (pCore 2 ↥H) hker h
  have hψrange : ψ.range = autOn H N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥H) y
      rw [← hφrange, hψapply h]
      exact ⟨h, rfl⟩
    · intro hx
      rw [← hφrange] at hx
      obtain ⟨h, hh⟩ := hx
      exact ⟨QuotientGroup.mk' (pCore 2 ↥H) h, by rw [hψapply h]; exact hh⟩
  have hVU3 : VU3Big L1 := str86_vU3Big_of_stated hk hFc hU3
  have hqL1 : CFSG.IsQuasisimple (oTwoQuot ↥L1) := isQuasisimple_oTwoQuot_of_u3 hk hFc hU3
  have hqH : CFSG.IsQuasisimple (oTwoQuot ↥H) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (u3QEquiv hF hSB hVU3).symm hqL1
  have hHnotC : ¬ H ≤ Subgroup.centralizer (N : Set G) := by
    intro hle
    have hNle : N ≤ Subgroup.centralizer (H : Set G) := Subgroup.le_centralizer_iff.mpr hle
    have hle' : N ≤ Z1 L1 L2 S ⊓
        Subgroup.centralizer ((L1 ⊔ S : Subgroup G) : Set G) := le_inf h1.1.1 hNle
    rw [hC] at hle'
    exact h1.2.1 (le_bot_iff.mp hle')
  have hLnontrivial : Nontrivial ↥(autOn H N) := by
    obtain ⟨h, hhH, hhC⟩ := Set.not_subset.mp hHnotC
    have hφne : φ ⟨h, hhH⟩ ≠ 1 := by
      intro heq
      have hmem' : Subgroup.inclusion hHN ⟨h, hhH⟩ ∈ (conjAct N).ker := by
        rw [MonoidHom.mem_ker]
        exact heq
      rw [show (conjAct N).ker =
        (Subgroup.centralizer (N : Set G)).subgroupOf
          (Subgroup.normalizer (N : Set G)) from Subgroup.normalizerMonoidHom_ker N] at hmem'
      exact hhC (Subgroup.mem_subgroupOf.mp hmem')
    refine ⟨⟨⟨φ ⟨h, hhH⟩, ?_⟩, ⟨1, (autOn H N).one_mem⟩, ?_⟩⟩
    · rw [← hφrange]
      exact ⟨_, rfl⟩
    · intro heq
      exact hφne (Subtype.ext_iff.mp heq)
  let ψL : oTwoQuot ↥H →* ↥(autOn H N) :=
    ψ.codRestrict (autOn H N) fun x => by
      rw [← hψrange]
      exact ⟨x, rfl⟩
  have hψLsurj : Function.Surjective ψL := by
    intro l
    have hl : (l : MulAut ↥N) ∈ ψ.range := by
      rw [hψrange]
      exact l.2
    obtain ⟨x, hx⟩ := hl
    exact ⟨x, Subtype.ext hx⟩
  let eC : oTwoQuot ↥H ⧸ Subgroup.center (oTwoQuot ↥H) ≃*
      ↥(autOn H N) ⧸ Subgroup.center ↥(autOn H N) :=
    CFSG.Quasithin.H13.KG14726.quotientCenterEquivOfSurjective hqH ψL hψLsurj
  let eQ : oTwoQuot ↥H ≃* oTwoQuot ↥L1 := u3QEquiv hF hSB hVU3
  let e1 : oTwoQuot ↥H ⧸ Subgroup.center (oTwoQuot ↥H) ≃*
      oTwoQuot ↥L1 ⧸ Subgroup.center (oTwoQuot ↥L1) :=
    QuotientGroup.congr (Subgroup.center (oTwoQuot ↥H)) (Subgroup.center (oTwoQuot ↥L1)) eQ
      (Subgroup.map_center_eq eQ)
  have h2k : 2 < 2 ^ k := by
    calc (2 : ℕ) < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hnq : ((3 : ℕ), 2 ^ k) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ k = 2 := by simpa using congrArg Prod.snd h
    rw [h2] at h2k
    norm_num at h2k
  rcases hU3 with hSU | hPSU
  · obtain ⟨eSU⟩ := hSU
    have hdat : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 k F :=
      ⟨Nat.prime_two, by omega, by rw [hFc, ← pow_mul, Nat.mul_comm]⟩
    have hcenterSU := CFSG.LieType.SemisimpleCentralizers.HeldLang.center_statedSU_eq
      (N := 3) hdat (by norm_num)
    let e2 : oTwoQuot ↥L1 ⧸ Subgroup.center (oTwoQuot ↥L1) ≃*
        StatedProj (StatedSU 3 (2 ^ k) F) :=
      (QuotientGroup.congr (Subgroup.center (oTwoQuot ↥L1))
        (Subgroup.center ↥(StatedSU 3 (2 ^ k) F)) eSU (Subgroup.map_center_eq eSU)).trans
        (QuotientGroup.quotientMulEquivOfEq hcenterSU)
    exact ⟨eC.symm.trans (e1.trans e2)⟩
  · obtain ⟨ePSU⟩ := hPSU
    have hsimplePSU : IsSimpleGroup (StatedProj (StatedSU 3 (2 ^ k) F)) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 k hFc 3 (by norm_num) hnq
    have hqPSU : CFSG.IsQuasisimple (StatedProj (StatedSU 3 (2 ^ k) F)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv ePSU hqL1
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hSUq := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (p := 2) (f := k) (F := F) hFc (by norm_num) hnq
    have hncPSU : ∃ a b : StatedProj (StatedSU 3 (2 ^ k) F), a * b ≠ b * a :=
      CFSG.Quasithin.F6.InspRest.exists_noncomm_statedProj
        (StatedSU 3 (2 ^ k) F) hSUq.1 hsimplePSU
    have hZbot : Subgroup.center (StatedProj (StatedSU 3 (2 ^ k) F)) = ⊥ :=
      CFSG.Quasithin.F7Two.center_eq_bot_of_isSimpleGroup hsimplePSU hncPSU
    let e2 : oTwoQuot ↥L1 ⧸ Subgroup.center (oTwoQuot ↥L1) ≃*
        StatedProj (StatedSU 3 (2 ^ k) F) :=
      (QuotientGroup.congr (Subgroup.center (oTwoQuot ↥L1))
        (Subgroup.center (StatedProj (StatedSU 3 (2 ^ k) F))) ePSU
        (Subgroup.map_center_eq ePSU)).trans
        ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot)
    exact ⟨eC.symm.trans (e1.trans e2)⟩


theorem str86_atom_irreducible {L1 L2 S : Subgroup G}
    {N : Subgroup G} (h1 : Str86AtomIn (L1 ⊔ S) (Z1 L1 L2 S) N)
    (hNabel : IsElemAbelian 2 N) :
    ∀ U : Subgroup ↥N,
      (∀ g ∈ autOn (L1 ⊔ S) N, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  classical
  let H : Subgroup G := L1 ⊔ S
  letI : CommGroup ↥N := commGroupOfElemAbelian hNabel
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn h1.1
  intro U hU
  let V : Subgroup G := U.map N.subtype
  have hVle : V ≤ N := Subgroup.map_subtype_le _
  have hVnormal : IsNormalIn H (Z1 L1 L2 S) V := by
    refine ⟨hVle.trans h1.1.1, ?_⟩
    intro h hh x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have hφmem : str86ConjHom H N hHN ⟨h, hh⟩ ∈ autOn H N := by
      rw [← str86ConjHom_range H N hHN]
      exact ⟨_, rfl⟩
    have hφu : (str86ConjHom H N hHN ⟨h, hh⟩) u ∈ U := hU _ hφmem u hu
    refine Subgroup.mem_map.mpr ⟨_, hφu, ?_⟩
    change (((conjAct N) (Subgroup.inclusion hHN ⟨h, hh⟩)) u : G) = h * (u : G) * h⁻¹
    exact Subgroup.normalizerMonoidHom_apply_apply_coe N (Subgroup.inclusion hHN ⟨h, hh⟩) u
  by_cases hVbot : V = ⊥
  · left
    rw [eq_bot_iff]
    intro u hu
    have hmem : N.subtype u ∈ V := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    rw [hVbot] at hmem
    have hu1 : u = 1 := Subtype.ext (Subgroup.mem_bot.mp hmem)
    rw [hu1]
    exact Subgroup.mem_bot.mpr rfl
  · right
    have hVeq : V = N := h1.2.2 V hVnormal hVbot hVle
    rw [eq_top_iff]
    intro u _
    have hmem : N.subtype u ∈ V := by rw [hVeq]; exact u.2
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hmem
    rwa [N.subtype_injective hvu] at hv


theorem str86_atom_displacement {L1 L2 S : Subgroup G} {k : ℕ}
    (hF : F112Hyp L1 L2 S) (hk : 2 ≤ k)
    {N : Subgroup G} (h1 : Str86AtomIn (L1 ⊔ S) (Z1 L1 L2 S) N)
    (hNabel : IsElemAbelian 2 N)
    (hSC : S ⊓ Subgroup.centralizer (N : Set G) = Q1 L1 L2 S)
    {t : G} (htQ2 : t ∈ Q2 L1 L2 S) (htQ1 : t ∉ Q1 L1 L2 S) (ht2 : t * t = 1)
    (hidx : (Subgroup.centralizer ({t} : Set G)).relIndex (Z1 L1 L2 S) ≤ (2 ^ k) ^ 2) :
    ∃ t' ∈ autOn (L1 ⊔ S) N, t' * t' = 1 ∧ t' ≠ 1 ∧
      (@fixV ↥N (commGroupOfElemAbelian hNabel)
        (Subgroup.zpowers (t' : MulAut ↥N))).index ≤ 2 ^ (3 * k) := by
  classical
  let H : Subgroup G := L1 ⊔ S
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn h1.1
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have htH : t ∈ H := (le_sup_right : S ≤ L1 ⊔ S) (hQ2S htQ2)
  let t' : ↥(autOn H N) :=
    ⟨str86ConjHom H N hHN ⟨t, htH⟩, by
      rw [← str86ConjHom_range H N hHN]
      exact ⟨_, rfl⟩⟩
  have ht'coe : ∀ u : ↥N, (((t' : MulAut ↥N) u : ↥N) : G) = t * (u : G) * t⁻¹ := by
    intro u
    change (((str86ConjHom H N hHN ⟨t, htH⟩) u : ↥N) : G) = t * (u : G) * t⁻¹
    exact Subgroup.normalizerMonoidHom_apply_apply_coe N (Subgroup.inclusion hHN ⟨t, htH⟩) u
  have ht'2 : t' * t' = 1 := by
    apply Subtype.ext
    change (str86ConjHom H N hHN ⟨t, htH⟩) * (str86ConjHom H N hHN ⟨t, htH⟩) = 1
    rw [← map_mul]
    have hpair : (⟨t, htH⟩ : ↥H) * ⟨t, htH⟩ = 1 := Subtype.ext (by simpa using ht2)
    rw [hpair, map_one]
  have ht'ne : t' ≠ 1 := by
    intro heq
    have htC : t ∈ Subgroup.centralizer (N : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have hfix : ((str86ConjHom H N hHN ⟨t, htH⟩) ⟨n, hn⟩ : ↥N) = ⟨n, hn⟩ := by
        have := congrArg (fun x : ↥(autOn H N) => ((x : MulAut ↥N) ⟨n, hn⟩)) heq
        simpa [t'] using this
      have hcoe : (((str86ConjHom H N hHN ⟨t, htH⟩) ⟨n, hn⟩ : ↥N) : G) = t * n * t⁻¹ :=
        Subgroup.normalizerMonoidHom_apply_apply_coe N (Subgroup.inclusion hHN ⟨t, htH⟩)
          ⟨n, hn⟩
      have h1' : t * n * t⁻¹ = n := by rw [← hcoe, hfix]
      calc n * t = (t * n * t⁻¹) * t := by rw [h1']
        _ = t * n := by group
    have hmem : t ∈ S ⊓ Subgroup.centralizer (N : Set G) := ⟨hQ2S htQ2, htC⟩
    rw [hSC] at hmem
    exact htQ1 hmem
  have hfix_eq : @fixV ↥N (commGroupOfElemAbelian hNabel)
      (Subgroup.zpowers (t' : MulAut ↥N)) =
      (Subgroup.centralizer ({t} : Set G)).subgroupOf N := by
    ext u
    rw [@CFSG.Quasithin.mem_fixV_zpowers_iff_apply ↥N (commGroupOfElemAbelian hNabel)
      (t' : MulAut ↥N) u]
    constructor
    · intro hu
      rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst h
      have hcoe := ht'coe u
      rw [hu] at hcoe
      have h1' : t * (u : G) * t⁻¹ = (u : G) := hcoe.symm
      have h := congrArg (fun x : G => x * t) h1'
      have h2 : (t * (u : G) * t⁻¹) * t = t * (u : G) := by group
      rw [h2] at h
      exact h
    · intro hu
      have huC : (u : G) ∈ Subgroup.centralizer ({t} : Set G) :=
        Subgroup.mem_subgroupOf.mp hu
      have hcomm : (u : G) * t = t * (u : G) :=
        (Subgroup.mem_centralizer_iff.mp huC t (Set.mem_singleton t)).symm
      have hcoe := ht'coe u
      apply Subtype.ext
      rw [hcoe]
      calc t * (u : G) * t⁻¹ = ((u : G) * t) * t⁻¹ := by rw [← hcomm]
        _ = (u : G) := by group
  have hidx1 : ((Subgroup.centralizer ({t} : Set G)).subgroupOf N).index =
      (Subgroup.centralizer ({t} : Set G)).relIndex N := by
    rw [← Subgroup.relIndex_top_right
        (H := (Subgroup.centralizer ({t} : Set G)).subgroupOf N),
      ← Subgroup.subgroupOf_self N,
      Subgroup.relIndex_subgroupOf (le_rfl : N ≤ N)]
  have hne : (Subgroup.centralizer ({t} : Set G)).relIndex (Z1 L1 L2 S) ≠ 0 := by
    have hd := Subgroup.relIndex_dvd_card (Subgroup.centralizer ({t} : Set G)) (Z1 L1 L2 S)
    exact (Nat.pos_of_dvd_of_pos hd Nat.card_pos).ne'
  have hmono : (Subgroup.centralizer ({t} : Set G)).relIndex N ≤
      (Subgroup.centralizer ({t} : Set G)).relIndex (Z1 L1 L2 S) :=
    Subgroup.relIndex_le_of_le_right (H := Subgroup.centralizer ({t} : Set G))
      (K := N) (L := Z1 L1 L2 S) h1.1.1 hne
  refine ⟨(t' : MulAut ↥N), t'.2, ?_, ?_, ?_⟩
  · have h := congrArg Subtype.val ht'2
    simpa using h
  · intro h1
    exact ht'ne (Subtype.ext h1)
  · calc (@fixV ↥N (commGroupOfElemAbelian hNabel)
          (Subgroup.zpowers (t' : MulAut ↥N))).index
        = ((Subgroup.centralizer ({t} : Set G)).subgroupOf N).index := by rw [hfix_eq]
      _ = (Subgroup.centralizer ({t} : Set G)).relIndex N := hidx1
      _ ≤ (Subgroup.centralizer ({t} : Set G)).relIndex (Z1 L1 L2 S) := hmono
      _ ≤ (2 ^ k) ^ 2 := hidx
      _ ≤ 2 ^ (3 * k) := by
          rw [← pow_mul]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)


theorem str86_natural_in_Z1_of_chief_one
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hc1 : IsChiefSeriesFrom (L1 ⊔ S) (Z1 L1 L2 S) (Z1 L1 L2 S) 1)
    {t : G} (htQ2 : t ∈ Q2 L1 L2 S) (htQ1 : t ∉ Q1 L1 L2 S) (ht2 : t * t = 1)
    (hidx : (Subgroup.centralizer ({t} : Set G)).relIndex (Z1 L1 L2 S) ≤ (2 ^ k) ^ 2) :
    ∃ (N : Subgroup G) (hN : IsElemAbelian 2 N), N ≤ Z1 L1 L2 S ∧ N ≠ ⊥ ∧
      P1 L1 L2 S ≤ Subgroup.normalizer (N : Set G) ∧
      S ⊓ Subgroup.centralizer (N : Set G) = Q1 L1 L2 S ∧
      @BinaryNaturalSU3 ↥N (commGroupOfElemAbelian hN) (autOn (L1 ⊔ S) N) ⊤ ⊥ k := by
  classical
  have hC : Z1 L1 L2 S ⊓ Subgroup.centralizer ((L1 ⊔ S : Subgroup G) : Set G) = ⊥ :=
    str86_centralizer_z1_sup_eq_bot hF hSB hk hFc hU3 hIIa
  obtain ⟨N, h1⟩ := str86_exists_atom hF hSB hk hFc hU3 hII
  have hNabel : IsElemAbelian 2 N :=
    (SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)).mono h1.1.1
  have hP1N : P1 L1 L2 S ≤ Subgroup.normalizer (N : Set G) :=
    str86_atom_normalizer_P1 hF hSB hk hFc hU3 hC hc1 h1
  have hSC : S ⊓ Subgroup.centralizer (N : Set G) = Q1 L1 L2 S :=
    str86_inf_centralizer_atom_eq_q1 hF hSB hk hFc hU3 hC h1
  have hperf : Group.IsPerfect ↥(autOn (L1 ⊔ S) N) :=
    str86_atom_action_perfect hF hSB hk hFc hU3 h1 hNabel
  have hirr : ∀ U : Subgroup ↥N,
      (∀ g ∈ autOn (L1 ⊔ S) N, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    str86_atom_irreducible h1 hNabel
  have hcenter : Nonempty (↥(autOn (L1 ⊔ S) N) ⧸
      Subgroup.center ↥(autOn (L1 ⊔ S) N) ≃* StatedProj (StatedSU 3 (2 ^ k) F)) :=
    str86_atom_center_quotient hF hSB hk hFc hU3 hC h1 hNabel
  obtain ⟨t', ht'mem, ht'2, ht'ne, ht'idx⟩ :=
    str86_atom_displacement hF hk h1 hNabel hSC htQ2 htQ1 ht2 hidx
  have hExp : ∀ w : ↥N, w * w = 1 := fun w => by
    apply Subtype.ext
    have := hNabel.2 w w.2
    simpa [pow_two] using this
  refine ⟨N, hNabel, h1.1.1, h1.2.1, hP1N, hSC, ?_⟩
  exact @u3NaturalOfSmallDisplacement_holds k hk F _ _ hFc ↥N
    (commGroupOfElemAbelian hNabel) _ hExp (autOn (L1 ⊔ S) N) hperf hirr hcenter
    ⟨t', ht'mem, ht'2, ht'ne, ht'idx⟩

theorem str86_natural_in_Z1
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) 2) :
    ∃ (N : Subgroup G) (hN : IsElemAbelian 2 N), N ≤ Z1 L1 L2 S ∧ N ≠ ⊥ ∧
      P1 L1 L2 S ≤ Subgroup.normalizer (N : Set G) ∧
      S ⊓ Subgroup.centralizer (N : Set G) = Q1 L1 L2 S ∧
      @BinaryNaturalSU3 ↥N (commGroupOfElemAbelian hN) (autOn (L1 ⊔ S) N) ⊤ ⊥ k := by
  classical
  have hc1 := str86_caseIIa_two_z1_series hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc
  obtain ⟨t, htQ2, htQ1, ht2, hidx⟩ :=
    str86_caseIIa_two_small_involution hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc
  exact str86_natural_in_Z1_of_chief_one hF hSB hk hFc hU3 hII hIIa hc1
    htQ2 htQ1 ht2 hidx

end CFSG.Quasithin.Stroth
