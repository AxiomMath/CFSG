module

public import CFSG.RankThree.PartTwo.Sec19.Step1919CoreProof
import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof
import CFSG.RankThree.CentralCover.FourGroupWitness
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec18

namespace Step1919CoreProof

variable {G : Type} [Group G] [Finite G]

theorem card_mul_card_range_dvd_of_faithful {K E Y : Subgroup G} (hEY : E ≤ Y)
    (hYE : Y ≤ Subgroup.normalizer (E : Set G)) (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hEc : IsMulCommutative E)
    (hfaith : ∀ y : Y, (y : G) ∈ E → Step1910Proof.quotAct hYK y = 1 → (y : G) = 1) :
    Nat.card E * Nat.card (E.normalizerMonoidHom.comp (Subgroup.inclusion hYE)).range ∣
      Nat.card (Step1910Proof.quotAct hYK).range := by
  set ψ := E.normalizerMonoidHom.comp (Subgroup.inclusion hYE) with hψ
  set ρ := Step1910Proof.quotAct hYK with hρ
  have hψapp : ∀ (y : Y) (e : E), ((ψ y e : E) : G) = y * e * (y : G)⁻¹ := fun y e => rfl
  have hker : ρ.ker ≤ ψ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    refine MulEquiv.ext fun e => Subtype.ext ?_
    rw [hψapp, MulAut.one_apply]
    have hyeE : (y : G) * e * (y : G)⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hYE y.2) e).mp e.2
    set w : Y := y * ⟨e, hEY e.2⟩ * y⁻¹ * (⟨e, hEY e.2⟩ : Y)⁻¹ with hw
    have hwE : (w : G) ∈ E := by
      simp only [hw, Subgroup.coe_mul, Subgroup.coe_inv]
      exact E.mul_mem hyeE (E.inv_mem e.2)
    have hwρ : ρ w = 1 := by
      rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv, hy]
      group
    have h1 := hfaith w hwE hwρ
    simp only [hw, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rwa [mul_inv_eq_one] at h1
  have hEker : E.subgroupOf Y ≤ ψ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun e => Subtype.ext ?_
    rw [hψapp, MulAut.one_apply]
    have h1 : (y : G) * e = e * y :=
      congrArg Subtype.val (hEc.is_comm.comm ⟨y, Subgroup.mem_subgroupOf.mp hy⟩ e)
    rw [h1, mul_inv_cancel_right]
  have hdisj : ρ.ker ⊓ E.subgroupOf Y = ⊥ := by
    rw [eq_bot_iff]
    intro y hyy
    obtain ⟨hy, hyE⟩ := Subgroup.mem_inf.mp hyy
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hfaith y (Subgroup.mem_subgroupOf.mp hyE) hy)
  have hsup := CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer
    (N := ρ.ker) (H := E.subgroupOf Y)
    (by rw [Subgroup.normalizer_eq_top_iff.mpr (MonoidHom.normal_ker ρ)]; exact le_top) hdisj
  have hEY' : Nat.card (E.subgroupOf Y) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv
  have hdvd : Nat.card ρ.ker * Nat.card E ∣ Nat.card ψ.ker := by
    rw [← hEY', ← hsup]
    exact Subgroup.card_dvd_of_le (sup_le hker hEker)
  have h1 : Nat.card ρ.ker * Nat.card ρ.range = Nat.card Y := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h2 : Nat.card ψ.ker * Nat.card ψ.range = Nat.card Y := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨m, Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ρ.ker)) ?_⟩
  rw [h1, ← h2, hm]
  ring

theorem center_eq_bot_of_faithful
    {M F J : Subgroup G} (hJM : J ∈ oTwoComponentsIn M)
    (hlist : IsList194 (J ⧸ CFSG.pCore 2 J) ∨ IsSmall194 (J ⧸ CFSG.pCore 2 J)) (hFJ : F ≤ J)
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9)
    (hfaith : ∀ f ∈ F, f ≠ 1 → ∃ j ∈ J, f * j * f⁻¹ * j⁻¹ ∉ CFSG.Open.pCoreOf 2 M) :
    Subgroup.center (J ⧸ CFSG.pCore 2 J) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect (J ⧸ CFSG.pCore 2 J) :=
    (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hJM).1
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  obtain ⟨n, -, ⟨ψ⟩⟩ := Step1911EndProof.exists_mulEquiv_SL_of_isList194_wide hlist hperf hz hz1
  have hψz : ψ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro s
    obtain ⟨t, rfl⟩ := ψ.surjective s
    rw [← map_mul, ← map_mul, hz t]
  have hz3 : z ^ 3 = 1 := ψ.injective (by
    rw [map_pow, Step1911EndProof.pow_three_eq_one_of_mem_center hψz, map_one])
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hzc : ∀ g : J ⧸ CFSG.pCore 2 J, g * z = z * g := Subgroup.mem_center_iff.mp hz
  set Fs := starIm J F with hFsdef
  have hF3 : IsPGroup 3 F := fun x => ⟨1, Subtype.ext (by simpa using hF.2 x x.2)⟩
  have hFs9 : Nat.card Fs = 9 := (Step1919EndProof.card_starIm hF3 hFJ).trans hF9
  have hFs : CFSG.Open.IsElemAbelian 3 Fs := Step1919EndProof.isElemAbelian_starIm hF
  have hzF : z ∉ Fs := by
    rintro ⟨f, hf, hfz⟩
    have hfF : (f : G) ∈ F := Subgroup.mem_subgroupOf.mp hf
    have hf1 : (f : G) ≠ 1 := by
      intro h
      apply hz1
      rw [← hfz, show f = 1 from Subtype.ext h, map_one]
    obtain ⟨j, hj, hjn⟩ := hfaith f hfF hf1
    apply hjn
    have h1 : ((f * ⟨j, hj⟩ * f⁻¹ * (⟨j, hj⟩ : J)⁻¹ : J) : J ⧸ CFSG.pCore 2 J) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv]
      have h2 : (f : J ⧸ CFSG.pCore 2 J) = z := hfz
      rw [h2, ← hzc]
      group
    rw [QuotientGroup.eq_one_iff, Step1911EndProof.mem_pCore_iff] at h1
    exact Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hJM (by simpa using h1)
  set V := Fs ⊔ Subgroup.zpowers z with hVdef
  have hV27 : Nat.card V = 27 := by
    rw [hVdef, Step1919NarrowRank.card_sup_zpowers_of_orderOf Fs hzo hzF (fun w _ => hzc w),
      hFs9]
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (Fs : Set (J ⧸ CFSG.pCore 2 J)) :=
    fun w hw => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [(Commute.zpow_left (Commute.symm (hzc h)) k).eq, mul_inv_cancel_right]
  have hVmem : ∀ v ∈ V, ∃ f ∈ Fs, ∃ k : ℤ, v = f * z ^ k := by
    intro v hv
    rw [← SetLike.mem_coe, hVdef, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hzN] at hv
    obtain ⟨f, hf, w, hw, rfl⟩ := hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ⟨f, hf, k, rfl⟩
  have hFsc : ∀ a ∈ Fs, ∀ b ∈ Fs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hFs.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hzk : ∀ (k : ℤ) (g : J ⧸ CFSG.pCore 2 J), g * z ^ k = z ^ k * g := fun k g =>
    (Commute.zpow_right (hzc g) k).eq
  have hV : CFSG.Open.IsElemAbelian 3 V := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun v hv => ?_⟩
    · obtain ⟨f, hf, k, hk⟩ := hVmem a a.2
      obtain ⟨f', hf', k', hk'⟩ := hVmem b b.2
      change (a : J ⧸ CFSG.pCore 2 J) * b = b * a
      rw [hk, hk']
      calc f * z ^ k * (f' * z ^ k') = f * (z ^ k * f') * z ^ k' := by group
        _ = f * (f' * z ^ k) * z ^ k' := by rw [← hzk k f']
        _ = (f * f') * (z ^ k * z ^ k') := by group
        _ = (f' * f) * (z ^ k' * z ^ k) := by
          rw [hFsc f hf f' hf', (Commute.zpow_zpow_self z k k').eq]
        _ = f' * (f * z ^ k') * z ^ k := by group
        _ = f' * (z ^ k' * f) * z ^ k := by rw [hzk k' f]
        _ = f' * z ^ k' * (f * z ^ k) := by group
    · obtain ⟨f, hf, k, rfl⟩ := hVmem v hv
      rw [(show Commute f (z ^ k) from hzk k f).mul_pow, hFs.2 f hf, one_mul, ← zpow_natCast,
        ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (J ⧸ CFSG.pCore 2 J)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hV (by rw [hV27]; norm_num)
  have h2 := Step1919EndProof.pRank_three_SL_le (F := GaloisField 2 n)
    Step1919EndProof.three_ne_zero_of_charTwo
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) ψ] at h2
  omega

end Step1919CoreProof

open Step1919CoreProof Step1919EndProof in
theorem step1919CoreSplit_of
    (hlie : Step1919CoreSplitLie) : Step1919CoreSplit := by
  intro G _ _ A c L E M hctx hLM h9 hX H hH hHM hJall hEN hcJ J hJ hP3 hEJF
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEe : ∀ e ∈ E, e ^ 3 = 1 := hE.1.2
  have hEH : E ≤ H := fun x hx => hH.2 (hctx.le_centralizer hx)
  have hEM : E ≤ M := hE.le_gamma.trans hctx.mem_scriptM.2
  set F := E ⊓ L with hFdef
  have hFE : F ≤ E := inf_le_left
  have hFN : Subgroup.normalizer (F : Set G) ≤ M :=
    (normalizer_le_gamma hFE (two_le_pRank_of_elemAbelian (isElemAbelian_of_le hE.1 hFE)
      h9.ge)).trans hctx.mem_scriptM.2
  have hJM : J ∈ oTwoComponentsIn M := hJ.1
  obtain ⟨hlist, hpar⟩ := hJall J hJ
  obtain ⟨y, hy3, hyc, hync⟩ := Step1919NarrowTools.exists_fixed_noncentral hJM hlist hpar
    hE.isPGroup hEe (hEN J hJ) hEH
  have hyE : (y : G) ∈ E := mem_of_le_centralizer hctx.toPartTwoStanding hctx.partTwoS_eq hEE
    hy3 fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hyc a ha)
  have hyn := Step1919Narrow.exists_not_mem_of_not_mem_center hJM y hync
  have hyF : (y : G) ∈ F := hEJF ▸ ⟨hyE, y.2⟩
  have hcE : c ∈ E :=
    mem_of_le_centralizer hctx.toPartTwoStanding hctx.partTwoS_eq hEE
      (hctx.mem_partTwoE.1.2 c (hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)))
      hctx.le_centralizer
  set V := E ⊓ cenMod M J with hVdef
  have hV : V = ⊥ := by
    by_contra hV1
    have hinv : ∀ z ∈ Subgroup.normalizer (F : Set G) ⊓ Subgroup.normalizer (E : Set G),
        (∃ k : ℕ, z ^ 3 ^ k = 1) → ∀ v ∈ V, z * v * z⁻¹ ∈ V := by
      intro z hz hz3 v hv
      have h1 := conj_mem_cenMod (hFN hz.1) hv.2
      have hJz : J.map (MulAut.conj z).toMonoidHom = J :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hP3 z hz hz3)
      rw [hJz] at h1
      exact ⟨(Subgroup.mem_normalizer_iff.mp hz.2 v).mp hv.1, h1⟩
    rcases eq_or_eq_of_conj_mem hctx h9 hX inf_le_left hV1 hinv with h | h
    · have hyV : (y : G) ∈ E ⊓ cenMod M J := by
        rw [h]
        exact hyF
      exact not_mem_cenMod hyn hyV.2
    · have hcV : c ∈ E ⊓ cenMod M J := by
        rw [h]
        exact hcE
      exact not_mem_cenMod (hcJ J hJ) hcV.2
  have hfaithE : ∀ e ∈ E, e ≠ 1 → ∃ j ∈ J, e * j * e⁻¹ * j⁻¹ ∉ CFSG.Open.pCoreOf 2 M := by
    intro e he he1
    by_contra hno
    push Not at hno
    have hev : e ∈ V := ⟨he, hEM he, hno⟩
    rw [hV] at hev
    exact he1 ((Subgroup.mem_bot).mp hev)
  set T : Set G := {g | g ∈ Subgroup.normalizer (F : Set G) ⊓ Subgroup.normalizer (E : Set G) ∧
    ∃ k : ℕ, g ^ 3 ^ k = 1} with hTdef
  set Y := Subgroup.closure T with hYdef
  have hYJ : Y ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.closure_le _).mpr fun g hg => hP3 g hg.1 hg.2
  have hYE : Y ≤ Subgroup.normalizer (E : Set G) :=
    (Subgroup.closure_le _).mpr fun g hg => hg.1.2
  have hEY : E ≤ Y := by
    intro e he
    refine Subgroup.subset_closure ⟨⟨?_, Subgroup.le_normalizer he⟩, 1,
      by rw [pow_one]; exact hEe e he⟩
    exact (Subgroup.centralizer_le_normalizer (F : Set G))
      (Subgroup.mem_centralizer_iff.mpr fun f hf => hEc f (hFE hf) e he)
  have hρfaith : ∀ g : Y, (g : G) ∈ E → Step1910Proof.quotAct hYJ g = 1 → (g : G) = 1 := by
    intro g hgE hg
    by_contra hg1
    obtain ⟨k, hk, hkn⟩ := hfaithE g hgE hg1
    apply hkn
    obtain ⟨j', hj', hact⟩ := Step1910Proof.quotAct_mk hYJ g ⟨k, hk⟩
    rw [hg, MulAut.one_apply] at hact
    have h1 : (⟨k, hk⟩ : J)⁻¹ * j' ∈ CFSG.pCore 2 J := QuotientGroup.eq.mp hact
    rw [Step1911EndProof.mem_pCore_iff] at h1
    have h2 : k⁻¹ * ((g : G) * k * (g : G)⁻¹) ∈ CFSG.Open.pCoreOf 2 J := by
      simpa [hj'] using h1
    have h3 : (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 J := by
      have := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J hk) _).mp h2
      rwa [show k * (k⁻¹ * ((g : G) * k * (g : G)⁻¹)) * k⁻¹ =
        (g : G) * k * (g : G)⁻¹ * k⁻¹ by group] at this
    exact Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hJM h3
  have hX216 : 216 ∣ Nat.card (E.normalizerMonoidHom.comp (Subgroup.inclusion hYE)).range := by
    have hXle : oUpperThreePrime (Sec4.autIn (Subgroup.normalizer (F : Set G)) E) ≤
        (E.normalizerMonoidHom.comp (Subgroup.inclusion hYE)).range := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro σ ⟨hσ, hσ3⟩
      obtain ⟨z, hzE, hzF, hz3, hzσ⟩ := exists_pow_of_mem_autIn hσ hσ3
      exact ⟨⟨z, Subgroup.subset_closure ⟨⟨hzF, hzE⟩, hz3⟩⟩, hzσ⟩
    have hcard : Nat.card (oUpperThreePrime
        (Sec4.autIn (Subgroup.normalizer (F : Set G)) E)) = 216 := by
      obtain ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ := hX
      have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
        rw [Nat.card_eq_fintype_card]
        decide
      rw [N.card_eq_card_quotient_mul_card_subgroup, Nat.card_congr eQ.toEquiv,
        Nat.card_congr eN.toEquiv, Nat.card_prod, hSL]
      simp
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hXle
  have h729 : 3 ^ 6 ∣ Nat.card (MulAut (J ⧸ CFSG.pCore 2 J)) := by
    have h1 : 27 * 216 ∣ Nat.card E *
        Nat.card (E.normalizerMonoidHom.comp (Subgroup.inclusion hYE)).range := by
      rw [hE.2]
      exact Nat.mul_dvd_mul_left 27 hX216
    have h2 := h1.trans ((card_mul_card_range_dvd_of_faithful hEY hYE hYJ hE.1.1
      hρfaith).trans (Subgroup.card_subgroup_dvd_card _))
    exact (by norm_num : (3 : ℕ) ^ 6 ∣ 27 * 216).trans h2
  have hFnc : ¬ IsCyclic (E ⊓ J : Subgroup G) := by
    rw [hEJF]
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (E ⊓ L : Subgroup G))
    have h1 : orderOf g = 9 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, h9]
    have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hEe _ (hFE g.2))
    have h2 := orderOf_dvd_of_pow_eq_one hg3
    rw [h1] at h2
    norm_num at h2
  obtain ⟨hA10, hpp⟩ : IsEmpty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
      IsProperParabolic (starIm J H) := by
    rcases hpar with h | ⟨-, hext⟩
    · exact h
    · exact (Step1911Proof.false_of_isExtOf hE hFnc le_rfl hEH hext).elim
  have hFJ : F ≤ J := by
    rw [← hEJF]
    exact inf_le_right
  have hZ := center_eq_bot_of_faithful hJM hlist hFJ (isElemAbelian_of_le hE.1 hFE) h9
    fun f hf hf1 => hfaithE f (hFE hf) hf1
  refine hlie G A c L E M hctx hLM h9 hX H hH hHM hJall hEN hcJ J hJ hP3 hpp hfaithE h729 hZ ?_
    hEJF
  rcases hlist with hlist | hsmall
  swap
  · rcases hsmall with hA6 | hU33
    ·
      exfalso
      obtain ⟨e⟩ := hA6
      refine not_dvd_card_mulAut_of_mulEquiv e ?_ ?_ h729
      · rw [nat_card_alternatingGroup, Nat.card_fin]
        decide
      · intro h9'
        have h4 :=
          CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.outer_card_le_four
        have hpos : 0 < Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
          (alternatingGroup (Fin 6))) := Nat.card_pos
        have h5 := Nat.le_of_dvd hpos h9'
        omega
    ·
      exact Or.inr (Or.inr hU33)
  rcases hlist with ⟨n, hn, h⟩ | h | h | h | h | h | h | h | h | ⟨b, b', hbb, h⟩ | h
  · exact Or.inl ⟨n, hn, h⟩
  ·
    exfalso
    obtain ⟨e⟩ := h
    refine not_dvd_card_mulAut_of_mulEquiv e ?_ not_nine_dvd_card_outer_projSU_four_two h729
    rw [Step1911Proof.card_projSU_four le_rfl]
    norm_num
  ·
    exact Or.inr (Or.inl h)
  ·
    exfalso
    obtain ⟨e⟩ := h
    refine not_dvd_card_mulAut_of_mulEquiv e ?_
      (not_nine_dvd_card_outer_projSL (by norm_num) le_rfl (by norm_num) (by norm_num)) h729
    rw [Step1911Proof.card_projSL (by norm_num) le_rfl]
    decide
  ·
    exfalso
    obtain ⟨e⟩ := h
    refine not_dvd_card_mulAut_of_mulEquiv e ?_
      (not_nine_dvd_card_outer_projSL (by norm_num) (by norm_num) le_rfl (by norm_num)) h729
    rw [Step1911Proof.card_projSL (by norm_num) (by norm_num)]
    decide
  ·
    exfalso
    obtain ⟨e⟩ := h
    refine not_dvd_card_mulAut_of_mulEquiv e ?_
      (not_nine_dvd_card_outer_projSL (by norm_num) le_rfl (by norm_num) (by norm_num)) h729
    rw [Step1911Proof.card_projSL (by norm_num) le_rfl]
    decide
  ·
    exfalso
    obtain ⟨e⟩ := h
    refine not_dvd_card_mulAut_of_mulEquiv e ?_
      (not_nine_dvd_card_outer_projSL (by norm_num) le_rfl (by norm_num) (by norm_num)) h729
    rw [Step1911Proof.card_projSL (by norm_num) le_rfl]
    decide
  ·
    exfalso
    obtain ⟨e⟩ := h
    refine not_dvd_card_mulAut_of_mulEquiv e ?_
      (not_nine_dvd_card_outer_projSL (by norm_num) le_rfl (by norm_num) (by norm_num)) h729
    rw [Step1911Proof.card_projSL (by norm_num) le_rfl]
    decide
  ·
    exfalso
    obtain ⟨e⟩ := h
    refine not_dvd_card_mulAut_of_mulEquiv e ?_ not_nine_dvd_card_outer_projSp h729
    rw [Step1911Proof.card_projSp 3 le_rfl]
    decide
  ·
    exfalso
    obtain ⟨e⟩ := h
    refine not_dvd_card_mulAut_of_mulEquiv e ?_ (not_nine_dvd_card_outer_projOmegaMinus hbb) h729
    rw [Step1911Proof.card_projOmegaMinus hbb]
    decide
  ·
    exfalso
    obtain ⟨e⟩ := h
    exact hA10.false e

end CFSG.RankThree.PartTwo.Sec19
