module

public import CFSG.RankThree.PartTwo.Sec18.Item182
public import CFSG.RankThree.PartTwo.Late.Item2010
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mem_mul_of_le_sup {L R N : Subgroup G} (hLN : L ≤ N) (hNLR : N ≤ L ⊔ R)
    (hLR : L ≤ Subgroup.normalizer (R : Set G)) (hNR : N ≤ Subgroup.normalizer (R : Set G))
    (hR : IsPGroup 2 R) {n : G} (hn : n ∈ N) :
    ∃ l ∈ L, l⁻¹ * n ∈ CFSG.Open.pCoreOf 2 N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn' : n ∈ ((L : Set G) * (R : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right L R hLR]
    exact hNLR hn
  obtain ⟨l, hl, r, hr, rfl⟩ := hn'
  refine ⟨l, hl, ?_⟩
  rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hrN : r ∈ N := by
    have := N.mul_mem (N.inv_mem (hLN hl)) hn
    simpa [mul_assoc] using this
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    (hR.to_le inf_le_right) ⟨hrN, hr⟩
  exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hNR hx⟩

omit [Finite G] in
theorem mem_pCore_iff_mem_pCoreOf {p : ℕ} {X : Subgroup G} (x : X) :
    x ∈ CFSG.pCore p X ↔ (x : G) ∈ CFSG.Open.pCoreOf p X := (CFSG.mem_openPCoreOf_iff x).symm

theorem isQuasisimple_quotient_of_le_sup {L R N : Subgroup G}
    (hq : CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)) (hLN : L ≤ N) (hNLR : N ≤ L ⊔ R)
    (hLR : L ≤ Subgroup.normalizer (R : Set G)) (hNR : N ≤ Subgroup.normalizer (R : Set G))
    (hR : IsPGroup 2 R) : CFSG.IsQuasisimple (N ⧸ CFSG.pCore 2 N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : L →* N ⧸ CFSG.pCore 2 N :=
    (QuotientGroup.mk' (CFSG.pCore 2 N)).comp (Subgroup.inclusion hLN) with hφ
  have hker : ∀ l : L, φ l = 1 ↔ (l : G) ∈ CFSG.Open.pCoreOf 2 N := by
    intro l
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_pCore_iff_mem_pCoreOf]
    rfl
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨l, hl, hln⟩ := exists_mem_mul_of_le_sup hLN hNLR hLR hNR hR n.2
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_eq_mk']
    refine ⟨⟨l⁻¹ * n, N.mul_mem (N.inv_mem (hLN hl)) n.2⟩,
      (mem_pCore_iff_mem_pCoreOf _).mpr hln, ?_⟩
    apply Subtype.ext
    simp
  have hkerle : φ.ker ≤ CFSG.pCore 2 L := by
    refine le_sSup ⟨inferInstance, ?_⟩
    have himg : (φ.ker).map L.subtype ≤ CFSG.Open.pCoreOf 2 N := by
      rintro _ ⟨l, hl, rfl⟩
      exact (hker l).mp hl
    have hp := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le himg
    exact hp.of_equiv ((φ.ker).equivMapOfInjective _ L.subtype_injective).symm
  have hle : CFSG.pCore 2 L ≤ φ.ker := by
    have hn : ((CFSG.pCore 2 L).map φ).Normal := (CFSG.pCore_normal (p := 2) (G := L)).map φ hsurj
    have hp : IsPGroup 2 ((CFSG.pCore 2 L).map φ) :=
      (CFSG.pCore_isPGroup (p := 2) (G := L)).map φ
    have hbot : (CFSG.pCore 2 L).map φ ≤ CFSG.pCore 2 (N ⧸ CFSG.pCore 2 N) :=
      le_sSup ⟨hn, hp⟩
    rw [pCore_quotient_pCore_eq_bot, le_bot_iff, Subgroup.map_eq_bot_iff] at hbot
    exact hbot
  set ψ := QuotientGroup.lift (CFSG.pCore 2 L) φ hle with hψ
  have hψs : Function.Surjective ψ := by
    intro q
    obtain ⟨l, rfl⟩ := hsurj q
    exact ⟨l, rfl⟩
  refine CFSG.LocalCores.isQuasisimple_of_surjective hq ψ hψs ?_
  intro x hx
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : φ l = 1 := hx
  have h2 : l ∈ CFSG.pCore 2 L := hkerle h1
  rw [(QuotientGroup.eq_one_iff l).mpr h2]
  exact Subgroup.one_mem _

omit [Finite G] in
theorem isSolvable_quotient_of_sup_eq {U V Y : Subgroup G} (hUY : U ≤ Y) (hVY : V ≤ Y)
    (hYU : Y ≤ Subgroup.normalizer (U : Set G)) (hUV : U ⊔ V = Y) (hV : Group.IsSolvable V)
    [(U.subgroupOf Y).Normal] : Group.IsSolvable (Y ⧸ U.subgroupOf Y) := by
  refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' (U.subgroupOf Y)).comp
    (Subgroup.inclusion hVY)) ?_
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hx : (x : G) ∈ ((U : Set G) * (V : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left U V (hVY.trans hYU), hUV]
    exact x.2
  obtain ⟨u, hu, v, hv, huv⟩ := hx
  refine ⟨⟨v, hv⟩, ?_⟩
  have hxuv : x = ⟨u, hUY hu⟩ * ⟨v, hVY hv⟩ := Subtype.ext huv.symm
  have hu1 : QuotientGroup.mk' (U.subgroupOf Y) (⟨u, hUY hu⟩ : Y) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hu)
  rw [hxuv, map_mul, hu1, one_mul]
  rfl

omit [Finite G] in
theorem isQuasisimple_of_mem_oTwoComponentsIn {X K : Subgroup G} (hK : K ∈ oTwoComponentsIn X) :
    CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) := by
  obtain ⟨hKX, ⟨-, -, hq⟩⟩ := mem_oTwoComponentsIn_iff.mp hK
  set e : K.subgroupOf X ≃* K := Subgroup.subgroupOfEquivOfLe hKX
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)) hq

omit [Finite G] in
theorem mem_oTwoComponentsIn_of_quasisimple {K Y : Subgroup G} (hKY : K ≤ Y)
    (hsn : (K.subgroupOf Y).IsSubnormal) (hK : ⁅K, K⁆ = K)
    (hq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K)) : K ∈ oTwoComponentsIn Y := by
  set e : K.subgroupOf Y ≃* K := Subgroup.subgroupOfEquivOfLe hKY
  refine mem_oTwoComponentsIn_iff.mpr ⟨hKY, ?_, hsn, ?_⟩
  · exact (Subgroup.isPerfect_iff).mpr (commutator_subgroupOf_eq hKY hK)
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e.symm (CFSG.pCore_map_iso 2 e.symm)) hq

theorem sup_le_pCoreOf_inf {M H R : Subgroup G} (hR : IsPGroup 2 R) (hRM : R ≤ M)
    (hHR : H ≤ Subgroup.normalizer (R : Set G)) :
    CFSG.Open.pCoreOf 2 (H ⊓ M) ⊔ R ≤ CFSG.Open.pCoreOf 2 ((H ⊔ R) ⊓ M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := CFSG.Open.pCoreOf 2 (H ⊓ M) with hTdef
  have hTH : T ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hTM : T ≤ M := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hTR2 : IsPGroup 2 (T ⊔ R : Subgroup G) := hT2.to_sup_of_normal_right' hR (hTH.trans hHR)
  have hYM : (H ⊔ R) ⊓ M ≤ Subgroup.normalizer ((T ⊔ R : Subgroup G) : Set G) := by
    intro x hx
    have hx' : x ∈ ((H : Set G) * (R : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right H R hHR]
      exact hx.1
    obtain ⟨y, hy, r, hr, rfl⟩ := hx'
    have hyM : y ∈ M := by
      have := M.mul_mem hx.2 (M.inv_mem (hRM hr))
      simpa using this
    refine Subgroup.mul_mem _ ?_ ?_
    · exact Subgroup.inf_normalizer_le_normalizer_sup T R
        ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M) ⟨hy, hyM⟩, hHR hy⟩
    · exact Subgroup.le_normalizer ((le_sup_right : R ≤ T ⊔ R) hr)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (le_inf (sup_le (hTH.trans le_sup_left) le_sup_right) (sup_le hTM hRM)) hYM hTR2

theorem sup_mem_scriptH {A M H R : Subgroup G} (h : Sec18Std G A M) (hH : H ∈ scriptH A M)
    (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) (hHR : H ≤ Subgroup.normalizer (R : Set G)) :
    H ⊔ R ∈ scriptH A M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := h.isSimpleGroup
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH := le_of_mem_scriptH₀ hH₀
  set L := inSubgroup perfectResidual H with hLdef
  set T := CFSG.Open.pCoreOf 2 (H ⊓ M) with hTdef
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hTH : T ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_inSubgroup_perfectResidual H
  have hLc : L ∈ oTwoComponentsIn H := hH₀.2.1
  have hRM : R ≤ M := le_of_le_normalizer_of_isPGroup_two h hR (hAH.trans hHR)
  have hHeq : H = L ⊔ A ⊔ T := hH₀.1
  set Y := H ⊔ R with hYdef
  have hHY : H ≤ Y := le_sup_left
  have hRY : R ≤ Y := le_sup_right
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) := sup_le hHR Subgroup.le_normalizer
  have hYLR : Y ≤ Subgroup.normalizer ((L ⊔ R : Subgroup G) : Set G) :=
    sup_le (fun x hx => Subgroup.inf_normalizer_le_normalizer_sup L R ⟨hHL hx, hHR hx⟩)
      (fun x hx => Subgroup.le_normalizer ((le_sup_right : R ≤ L ⊔ R) hx))
  have hLRY : L ⊔ R ≤ Y := sup_le (hLH.trans hHY) hRY
  have hLRn : ((L ⊔ R).subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLRY).mpr hYLR
  have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
    fun a ha => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M) ⟨hAH ha, sec18Std_le h ha⟩
  have hATs := isSolvable_sup_of_le_normalizer hA.1.1 hT2 hAT
  have hATY : A ⊔ T ≤ Y := sup_le (hAH.trans hHY) (hTH.trans hHY)
  have hsupY : (L ⊔ R) ⊔ (A ⊔ T) = Y := by
    apply le_antisymm (sup_le hLRY hATY)
    have hHle : H ≤ (L ⊔ R) ⊔ (A ⊔ T) := by
      calc H = L ⊔ A ⊔ T := hHeq
        _ ≤ _ := sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans
          le_sup_right)) (le_sup_right.trans le_sup_right)
    exact sup_le hHle (le_sup_right.trans le_sup_left)
  have hq : Group.IsSolvable (Y ⧸ (L ⊔ R).subgroupOf Y) :=
    isSolvable_quotient_of_sup_eq hLRY hATY hYLR hsupY hATs
  set N := inSubgroup perfectResidual Y with hNdef
  have hNLR : N ≤ L ⊔ R := inSubgroup_perfectResidual_le_of_isSolvable hLRY hq
  have hLN : L ≤ N := le_inSubgroup_perfectResidual
    (commutator_eq_of_mem_oTwoComponentsIn hLc) (hLH.trans hHY)
  have hNY : N ≤ Y := Subgroup.map_subtype_le _
  have hNq : CFSG.IsQuasisimple (N ⧸ CFSG.pCore 2 N) :=
    isQuasisimple_quotient_of_le_sup (isQuasisimple_of_mem_oTwoComponentsIn hLc) hLN hNLR
      (hLH.trans hHR) (hNY.trans hYR) hR
  have hNn : (N.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr
      (le_normalizer_inSubgroup_perfectResidual Y)
  have hNc : N ∈ oTwoComponentsIn Y :=
    mem_oTwoComponentsIn_of_quasisimple hNY hNn.isSubnormal
      (commutator_inSubgroup_perfectResidual Y) hNq
  have hTR := sup_le_pCoreOf_inf hR hRM hHR
  have hTO : T ≤ CFSG.Open.pCoreOf 2 (Y ⊓ M) := le_sup_left.trans hTR
  have hRO : R ≤ CFSG.Open.pCoreOf 2 (Y ⊓ M) := le_sup_right.trans hTR
  refine ⟨?_, ?_, hNc, ?_⟩
  ·
    intro htop
    have hN : Subgroup.normalizer (R : Set G) = ⊤ := by
      rw [eq_top_iff, ← htop]
      exact hYR
    exact normalizer_ne_top_of_isPGroup_two h.nonabelian hR hR1 hN
  ·
    apply le_antisymm
    · have hHle : H ≤ N ⊔ A ⊔ CFSG.Open.pCoreOf 2 (Y ⊓ M) := by
        calc H = L ⊔ A ⊔ T := hHeq
          _ ≤ _ := sup_le (sup_le (hLN.trans (le_sup_left.trans le_sup_left))
            (le_sup_right.trans le_sup_left)) (hTO.trans le_sup_right)
      exact sup_le hHle (hRO.trans le_sup_right)
    · exact sup_le (sup_le hNY (hAH.trans hHY))
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
  ·
    intro heq
    apply hH₀.2.2
    refine le_antisymm (pCoreOf_le_pCoreOf_inf h hAH) ?_
    have h1 : T ≤ CFSG.Open.pCoreOf 2 Y := heq ▸ hTO
    have h2 : CFSG.Open.pCoreOf 2 Y ⊓ H ≤ CFSG.Open.pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y (hHY hx), Subgroup.le_normalizer hx⟩)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le inf_le_left)
    exact (le_inf h1 hTH).trans h2

theorem le_pCoreOf_of_mem_scriptHStar {A M H R : Subgroup G} (h : Sec18Std G A M)
    (hH : H ∈ scriptHStar A M) (hR : IsPGroup 2 R) (hHR : H ≤ Subgroup.normalizer (R : Set G)) :
    R ≤ CFSG.Open.pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hR1 : R = ⊥
  · rw [hR1]
    exact bot_le
  have hmem := sup_mem_scriptH h hH.prop hR hR1 hHR
  have hle : H ⊔ R ≤ H := hH.2 hmem le_sup_left
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_sup_right.trans hle) hHR hR

theorem generalizedFitting_eq_of_mem_scriptHStar {A M H : Subgroup G} (h : Sec18Std G A M)
    (hH : H ∈ scriptHStar A M) (hH2 : CFSG.Open.pCoreOf 2 H ≠ ⊥) :
    CFSG.generalizedFitting H = CFSG.pCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 H with hQ
  set X := Subgroup.normalizer (Q : Set G) with hX
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hHX : H ≤ X := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hX2 : CFSG.Assembly.IsTwoLocal X := ⟨Q, hH2, hQ2, rfl⟩
  have h1 : CFSG.Open.pCoreOf 2 X ≤ Q :=
    le_pCoreOf_of_mem_scriptHStar h hH (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
      (hHX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
  have h2 : Q ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (CFSG.LieType.BorelTits.pCoreOf_le 2 H
      |>.trans hHX) le_rfl hQ2
  have hQX : CFSG.Open.pCoreOf 2 X = Q := le_antisymm h1 h2
  have hcen : H ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
    intro x hx
    have heq : CFSG.Assembly.pCoreOf 2 X = Q := hQX
    have hx2 : x ∈ Subgroup.centralizer (CFSG.Assembly.pCoreOf 2 X : Set G) := by
      rw [heq]
      exact hx.2
    have h3 := h.charTwoType X hX2 ⟨hHX hx.1, hx2⟩
    rw [heq] at h3
    exact h3
  have hP : CFSG.IsCharacteristicP 2 H := by
    change Subgroup.centralizer (CFSG.pCore 2 H : Set H) ≤ CFSG.pCore 2 H
    intro x hx
    have hxQ : (x : G) ∈ Q := by
      refine hcen ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      obtain ⟨q', hq', rfl⟩ := hq
      have hq'' : q' ∈ CFSG.pCore 2 H := by exact hq'
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx q' hq'')
    exact (mem_pCore_iff_mem_pCoreOf x).mpr hxQ
  exact (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore H 2).mp hP

end CFSG.RankThree.PartTwo.Sec18
