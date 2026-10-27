module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22c
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.Quasithin.Background.BlueprintB2Bridge
import CFSG.Quasithin.Background.BlueprintB2Thompson
import CFSG.GroupTheory.ThompsonAxB
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.RankThreeUC.TheoremDSolvableQuotient
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22p22e_isElemAbelian_map {p : ℕ} {B : Subgroup G} (hB : IsElemAbelian p B) (f : G →* G) :
    IsElemAbelian p (B.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · rcases a with ⟨_, a', ha', rfl⟩
    rcases b with ⟨_, b', hb', rfl⟩
    apply Subtype.ext
    show f a' * f b' = f b' * f a'
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hB.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hB.2 x hx, map_one]

theorem uc22p22e_isPGroup_of_elem {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := by
  intro g
  refine ⟨1, ?_⟩
  have := hE.2 (g : G) g.2
  exact Subtype.ext (by simpa using this)

theorem uc22p22e_jOf_le {M T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    jOf T ≤ jOf M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ∀ S : Subgroup G, jOf S = CFSG.Quasithin.thompsonJ S := fun S =>
    CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ S
  rw [h1, h1]
  refine iSup₂_le fun A hA => ?_
  refine le_iSup₂_of_le A ?_ le_rfl
  obtain ⟨hAT, hAel, hAmax⟩ := hA
  refine ⟨hAT.trans hT.le, hAel, fun B hBM hBel => ?_⟩
  obtain ⟨k, hk, hkB⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_conj_le_of_isSylowOf hT hBM
      (uc22p22e_isPGroup_of_elem hBel)
  have hB'T : B.map (MulAut.conj k⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    have := hkB x hx
    simpa using this
  have h2 := hAmax _ hB'T (uc22p22e_isElemAbelian_map hBel _)
  rwa [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective] at h2

theorem uc22p22e_jOf_le_self (X : Subgroup G) : jOf X ≤ X := Subgroup.map_subtype_le _

theorem uc22p22e_uCore_le {M T : Subgroup G} (hTM : T ≤ M) : uCore M T ≤ M := by
  refine iSup_le fun m => ?_
  rintro _ ⟨z, hz, rfl⟩
  have hzT : z ∈ T := CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le T hz
  exact M.mul_mem (M.mul_mem m.2 (hTM hzT)) (M.inv_mem m.2)

theorem uc22p22e_omegaOneCenterIn_le_uCore (M T : Subgroup G) :
    CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ uCore M T := by
  refine le_iSup_of_le (1 : M) ?_
  intro z hz
  exact Subgroup.mem_map.2 ⟨z, hz, by simp⟩

theorem uc22p22e_inCalV_U (D : Data G) : InCalV D.M D.U := by
  obtain ⟨-, hUel⟩ := uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM
  refine ⟨?_, uc22p22e_uCore_le D.sylowM.le, le_normalizer_uCore D.M D.T, hUel⟩
  intro h
  have hT1 : D.T ≠ ⊥ := ne_bot_of_isSylowOf_two D.maxLocal.1 D.sylowM
  apply CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_ne_bot D.sylowM.isPGroup hT1
  exact le_bot_iff.1 (h ▸ uc22p22e_omegaOneCenterIn_le_uCore D.M D.T)

theorem uc22p22e_pCoreOf_le_T (D : Data G) : pCoreOf 2 D.M ≤ D.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := D.sylowM.exists_sylow_eq_subgroupOf
  have h := CFSG.fitting_pCore_le_sylow S
  rw [hS] at h
  exact Subgroup.map_le_iff_le_comap.2 h

theorem uc22p22e_conj_jOf {T : Subgroup G} {y : G} (h : ∀ x ∈ jOf T, y * x * y⁻¹ ∈ T) :
    ∀ x ∈ jOf T, y * x * y⁻¹ ∈ jOf T := by
  have h1 : ∀ S : Subgroup G, jOf S = CFSG.Quasithin.thompsonJ S := fun S =>
    CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ S
  rw [h1] at h ⊢
  have key : CFSG.Quasithin.thompsonJ T ≤
      (CFSG.Quasithin.thompsonJ T).comap (MulAut.conj y).toMonoidHom := by
    refine iSup₂_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_iSup₂_of_le (A.map (MulAut.conj y).toMonoidHom) ?_ le_rfl
    have hAJ : A ≤ CFSG.Quasithin.thompsonJ T := le_iSup₂_of_le A hA le_rfl
    obtain ⟨hAT, hAel, hAmax⟩ := hA
    refine ⟨?_, uc22p22e_isElemAbelian_map hAel _, fun B hBT hBel => ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact h a (hAJ ha)
    · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
      exact hAmax B hBT hBel
  intro x hx
  exact key hx

theorem uc22p22e_mem_omegaZJ {T : Subgroup G} {z : G} :
    z ∈ omegaZJ22 T ↔ z ∈ jOf T ∧ (∀ j ∈ jOf T, j * z = z * j) ∧ z ^ 2 = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxJ, hxc, hx2⟩ := CFSG.Quasithin.BlueprintB2.mem_centerTorsion_iff.1 hx
    refine ⟨⟨x, hxJ, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨j, hj, rfl⟩
      exact congrArg Subtype.val (hxc j hj)
    · have := congrArg Subtype.val hx2
      simpa using this
  · rintro ⟨⟨x, hxJ, rfl⟩, hc, h2⟩
    refine ⟨x, CFSG.Quasithin.BlueprintB2.mem_centerTorsion_iff.2 ⟨hxJ, fun k hk => ?_, ?_⟩, rfl⟩
    · exact Subtype.ext (hc (k : G) ⟨k, hk, rfl⟩)
    · exact Subtype.ext (by simpa using h2)

theorem uc22p22e_mem_omegaZJ' {T : Subgroup G} {z : G} :
    z ∈ omegaZJ22 T ↔ z ∈ T ∧ (∀ j ∈ jOf T, j * z = z * j) ∧ z ^ 2 = 1 := by
  constructor
  · intro h
    obtain ⟨hJ, hc, h2⟩ := uc22p22e_mem_omegaZJ.1 h
    exact ⟨uc22p22e_jOf_le_self T hJ, hc, h2⟩
  · rintro ⟨hzT, hc, h2⟩
    refine ⟨⟨z, hzT⟩, ?_, rfl⟩
    refine (CFSG.Quasithin.BlueprintB2.mem_elemThompsonCenterTorsion_iff_centralizer).2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact Subtype.ext (hc (j : G) ⟨j, hj, rfl⟩)
    · exact Subtype.ext (by simpa using h2)

theorem uc22p22e_omegaZJ_le_jOf (T : Subgroup G) : omegaZJ22 T ≤ jOf T :=
  fun _ hz => (uc22p22e_mem_omegaZJ.1 hz).1

theorem uc22p22e_conj_omegaZJ {T : Subgroup G} {y : G} (hy : ∀ x ∈ jOf T, y * x * y⁻¹ ∈ jOf T)
    (hy' : ∀ x ∈ jOf T, y⁻¹ * x * y ∈ jOf T) :
    ∀ z ∈ omegaZJ22 T, y * z * y⁻¹ ∈ omegaZJ22 T := by
  intro z hz
  obtain ⟨hzJ, hzc, hz2⟩ := uc22p22e_mem_omegaZJ.1 hz
  refine uc22p22e_mem_omegaZJ.2 ⟨hy z hzJ, fun j hj => ?_, ?_⟩
  · have h1 := hzc _ (hy' j hj)
    calc j * (y * z * y⁻¹) = y * ((y⁻¹ * j * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * j * y)) * y⁻¹ := by rw [h1]
      _ = (y * z * y⁻¹) * j := by group
  · rw [conj_pow, hz2]
    simp

theorem uc22p22e_normalizes_jOf_T (D : Data G) :
    ∀ y ∈ D.T, ∀ x ∈ jOf D.T, y * x * y⁻¹ ∈ jOf D.T := by
  intro y hy
  refine uc22p22e_conj_jOf (fun x hx => ?_)
  exact D.T.mul_mem (D.T.mul_mem hy (uc22p22e_jOf_le_self D.T hx)) (D.T.inv_mem hy)

theorem uc22p22e_thompson {Y Vm : Type} [Group Y] [Finite Y] [Group Vm] [Finite Vm]
    (φ : Y →* MulAut Vm) (hV : IsPGroup 2 Vm) {B : Subgroup Y} (hB : IsPGroup 2 B) {c : Y}
    (hc : Odd (orderOf c)) (hcB : ∀ b ∈ B, φ c * φ b = φ b * φ c)
    (hfix : ∀ r : Vm, (∀ b ∈ B, φ b r = r) → φ c r = r) : φ c = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := Subgroup.zpowers c
  let α : ↥A →* MulAut Vm := φ.comp A.subtype
  let β : ↥B →* MulAut Vm := φ.comp B.subtype
  have hA2 : ¬ 2 ∣ Nat.card A := by
    rw [Nat.card_zpowers]
    have := Nat.odd_iff.1 hc
    omega
  have hcomm : ∀ (a : ↥A) (b : ↥B), α a * β b = β b * α a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hb' : Commute (φ c) (φ b) := hcB b hb
    simp only [α, β, MonoidHom.comp_apply, Subgroup.coe_subtype, map_zpow]
    exact (hb'.zpow_left k).eq
  have hfix' : ∀ (a : ↥A) (r : Vm), (∀ b : ↥B, β b r = r) → α a r = r := by
    rintro ⟨a, ha⟩ r hr
    have hcr : φ c r = r := hfix r (fun b hb => hr ⟨b, hb⟩)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hmem : φ c ∈ MulAction.stabilizer (MulAut Vm) r := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hcr
    have h2 := (MulAction.stabilizer (MulAut Vm) r).zpow_mem hmem k
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h2
    simp only [α, MonoidHom.comp_apply, Subgroup.coe_subtype, map_zpow]
    exact h2
  have := CFSG.GroupTheory.thompson_A_times_B hV hA2 hB α β hcomm hfix'
  exact this ⟨c, Subgroup.mem_zpowers c⟩

theorem uc22p22e_frattini {H : Type*} [Group H] [Finite H] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {K S P : Subgroup H} [K.Normal] (hS : CFSG.ABGLocalTools.IsSylowOf q S K)
    (hP : IsPGroup p P) (hPK : P ⊓ K = ⊥) (hnc : ¬ IsCyclic P) :
    ∃ X : Subgroup H, IsPGroup p X ∧ ¬ IsCyclic X ∧ X ≤ Subgroup.normalizer (S : Set H) := by
  classical
  obtain ⟨S₀, rfl⟩ := hS
  set N : Subgroup H := Subgroup.normalizer ((S₀.map K.subtype : Subgroup H) : Set H) with hN
  have hF : N ⊔ K = ⊤ := Sylow.normalizer_sup_eq_top S₀
  set π : H →* H ⧸ K := QuotientGroup.mk' K with hπ
  set Q : Subgroup (H ⧸ K) := P.map π with hQ
  set W : Subgroup H := N ⊓ Q.comap π with hW
  have hπW : W.map π = Q := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : y ∈ N ⊔ K := hF ▸ Subgroup.mem_top y
      obtain ⟨n, hn, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hy'
      have hk1 : π k = 1 := (QuotientGroup.eq_one_iff k).2 hk
      have hπ1 : π (n * k) = π n := by
        rw [map_mul, hk1, mul_one]
      refine ⟨n, ⟨hn, ?_⟩, hπ1.symm⟩
      show π n ∈ Q
      rw [← hπ1]
      exact Subgroup.mem_map_of_mem _ hy
  obtain ⟨X₀⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥W))
  set X : Subgroup H := (X₀ : Subgroup ↥W).map W.subtype with hX
  have hXW : X ≤ W := Subgroup.map_subtype_le _
  have hQp : IsPGroup p ↥Q := hP.map π
  have hWQ : ∀ w : ↥W, π (w : H) ∈ Q := fun w => w.2.2
  let f : ↥W →* ↥Q := (π.comp W.subtype).codRestrict Q hWQ
  have hf : Function.Surjective f := by
    rintro ⟨q', hq'⟩
    rw [← hπW] at hq'
    obtain ⟨w, hw, hwq⟩ := hq'
    exact ⟨⟨w, hw⟩, Subtype.ext hwq⟩
  have htop : ((X₀.mapSurjective hf : Sylow p ↥Q) : Subgroup ↥Q) = ⊤ := by
    symm
    exact (X₀.mapSurjective hf).is_maximal' (hQp.of_equiv Subgroup.topEquiv.symm) le_top
  have hsurj : ∀ q' ∈ Q, ∃ x ∈ X, π x = q' := by
    intro q' hq'
    have h1 : (⟨q', hq'⟩ : ↥Q) ∈ ((X₀.mapSurjective hf : Sylow p ↥Q) : Subgroup ↥Q) := by
      rw [htop]; trivial
    rw [Sylow.coe_mapSurjective] at h1
    obtain ⟨x, hx, hxq⟩ := h1
    exact ⟨(x : H), ⟨x, hx, rfl⟩, congrArg Subtype.val hxq⟩
  refine ⟨X, X₀.isPGroup'.map W.subtype, ?_, fun x hx => (hXW hx).1⟩
  intro hXc
  apply hnc
  let g : ↥X →* ↥Q := (π.comp X.subtype).codRestrict Q (fun x => (hXW x.2).2)
  have hg : Function.Surjective g := by
    rintro ⟨q', hq'⟩
    obtain ⟨x, hx, hxq⟩ := hsurj q' hq'
    exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩
  haveI : IsCyclic ↥Q := isCyclic_of_surjective g hg
  let h : ↥P →* ↥Q := (π.comp P.subtype).codRestrict Q (fun x => Subgroup.mem_map_of_mem _ x.2)
  have hinj : Function.Injective h := by
    intro a b hab
    have hab' : π (a : H) = π (b : H) := congrArg Subtype.val hab
    have h1 : (a : H)⁻¹ * (b : H) ∈ K := by
      rw [← QuotientGroup.eq]
      exact hab'
    have h2 : (a : H)⁻¹ * (b : H) ∈ P ⊓ K := ⟨P.mul_mem (P.inv_mem a.2) b.2, h1⟩
    rw [hPK, Subgroup.mem_bot] at h2
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  exact isCyclic_of_injective h hinj

theorem uc22p22e_frattini_sub {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {H₀ K S P : Subgroup G} (hKH : K ≤ H₀) (hHK : H₀ ≤ normalizer (K : Set G))
    (hS : CFSG.ABGLocalTools.IsSylowOf q S K) (hP : IsPGroup p P) (hPH : P ≤ H₀)
    (hPK : P ⊓ K = ⊥) (hnc : ¬ IsCyclic P) :
    ∃ X : Subgroup G, X ≤ H₀ ∧ IsPGroup p X ∧ ¬ IsCyclic X ∧ X ≤ normalizer (S : Set G) := by
  haveI : (K.subgroupOf H₀).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHK
  obtain ⟨hSK, hSp, hSidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hS
  have hSH : S ≤ H₀ := hSK.trans hKH
  have hS' : CFSG.ABGLocalTools.IsSylowOf q (S.subgroupOf H₀) (K.subgroupOf H₀) := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨fun x hx => hSK hx, hSp.comap_subtype, ?_⟩
    rwa [Subgroup.relIndex_subgroupOf hKH]
  have hP' : IsPGroup p (P.subgroupOf H₀) := hP.comap_subtype
  have hPK' : P.subgroupOf H₀ ⊓ K.subgroupOf H₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxP, hxK⟩
    have h1 : (x : G) ∈ P ⊓ K := ⟨hxP, hxK⟩
    rw [hPK, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  have hnc' : ¬ IsCyclic ↥(P.subgroupOf H₀) := by
    intro hc
    exact hnc (isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hPH).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPH).surjective)
  obtain ⟨X', hX'p, hX'nc, hX'N⟩ := uc22p22e_frattini hS' hP' hPK' hnc'
  refine ⟨X'.map H₀.subtype, Subgroup.map_subtype_le _, hX'p.map _, ?_, ?_⟩
  · intro hc
    exact hX'nc (isCyclic_of_injective
      (Subgroup.equivMapOfInjective X' H₀.subtype H₀.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective X' H₀.subtype H₀.subtype_injective).injective)
  · rintro _ ⟨x', hx', rfl⟩
    have hx'N := hX'N hx'
    rw [Subgroup.mem_normalizer_iff] at hx'N ⊢
    intro h
    constructor
    · intro hh
      exact (hx'N ⟨h, hSH hh⟩).1 hh
    · intro hh
      have hhH : h ∈ H₀ := by
        have h1 : (x' : G) * h * (x' : G)⁻¹ ∈ H₀ := hSH hh
        have := H₀.mul_mem (H₀.mul_mem (H₀.inv_mem x'.2) h1) x'.2
        simpa [mul_assoc] using this
      exact (hx'N ⟨h, hhH⟩).2 hh

theorem uc22p22e_not_isCyclic_sylow {p : ℕ} (hp : p.Prime) {M P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P M) (hr : 2 ≤ CFSG.Open.pRank p M) :
    ¬ IsCyclic P := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEM, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt M
  obtain ⟨k, hk, hkE⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_conj_le_of_isSylowOf hP hEM
      (uc22p22e_isPGroup_of_elem hEel)
  intro hcyc
  have hE'P : E.map (MulAut.conj k⁻¹).toMonoidHom ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    have := hkE x hx
    simpa using this
  haveI : IsCyclic ↥P := hcyc
  haveI : IsCyclic ↥(E.map (MulAut.conj k⁻¹).toMonoidHom) := Subgroup.isCyclic_of_le hE'P
  have hE'el := uc22p22e_isElemAbelian_map hEel (MulAut.conj k⁻¹).toMonoidHom
  have hexp : Monoid.exponent ↥(E.map (MulAut.conj k⁻¹).toMonoidHom) ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
      have h := hE'el.2 (x : G) x.2
      rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      exact h)
  rw [IsCyclic.exponent_eq_card, Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective,
    hEcard] at hexp
  have h1 : p ^ CFSG.Open.pRank p M ≤ p ^ 1 := by
    rw [pow_one]
    exact Nat.le_of_dvd hp.pos hexp
  have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  omega

theorem uc22p22e_calCGS_le (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig) {X S : Subgroup G}
    (hXM : X ≤ D.M) (hXp : IsPGroup p X) (hXc : ¬ IsCyclic X) (hXS : X ≤ normalizer (S : Set G))
    (hST : S ≤ D.T) : UC6.calCGS S ≤ D.M := by
  unfold UC6.calCGS
  refine iSup_le fun C => iSup_le fun hC1 => iSup_le fun hC2 => iSup_le fun hC3 => ?_
  haveI := hC3
  have hCmap : (C.subgroupOf S).map S.subtype = C := Subgroup.map_subgroupOf_eq_of_le hC2
  have key : ∀ y ∈ normalizer (S : Set G), ∀ c ∈ C, y * c * y⁻¹ ∈ C := by
    intro y hy c hc
    have h1 : c ∈ (C.subgroupOf S).map S.subtype := by rw [hCmap]; exact hc
    have h2 := uc22br4_conj_mem_map_of_characteristic (D := C.subgroupOf S) hy h1
    rwa [hCmap] at h2
  have hXC : X ≤ normalizer (C : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact key x (hXS hx) h hh
    · intro hh
      have := key x⁻¹ (hXS (X.inv_mem hx)) _ hh
      simpa [mul_assoc] using this
  have hCp : IsPGroup 2 C := (D.sylowM.isPGroup.to_le (hC2.trans hST))
  exact PartTwo.normalizer_le_of_noncyclic D h61 hp hXM hXp hXc hC1 hCp hXC

theorem uc22p22e_solvable_autOn (D : Data G) (hsolv : Group.IsSolvable ↥D.M) :
    Group.IsSolvable ↥(CFSG.Quasithin.autOn D.M D.U) := by
  have hMN : D.M ≤ normalizer (D.U : Set G) := le_normalizer_uCore D.M D.T
  haveI := hsolv
  haveI : Group.IsSolvable ↥(D.M.subgroupOf (normalizer (D.U : Set G))) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hMN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hMN).symm.surjective
  exact Group.isSolvable_of_surjective
    (f := (CFSG.Quasithin.conjAct D.U).subgroupMap (D.M.subgroupOf (normalizer (D.U : Set G))))
    (MonoidHom.subgroupMap_surjective _ _)

theorem uc22p22e_pow_six (D : Data G) (hsolv : Group.IsSolvable ↥D.M) :
    ∀ x ∈ jOf D.M, x ^ 6 ∈ centralizer (D.U : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCT : CFSG.QuasithinUnique.CharTwo D.M := D.standing.charTwo D.M D.maxLocal.1
  have hT : CFSG.QuasithinUnique.IsSylowTwoOf D.T D.M :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM
  have hV : D.U = CFSG.Quasithin.conjClosure (CFSG.Open.quasithinOmegaOneCenter D.T) D.M :=
    uCore_eq_conjClosure D.M D.T
  intro x hx
  have h1 : jOf D.M = CFSG.Quasithin.thompsonJ D.M :=
    CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ D.M
  rw [h1] at hx
  exact pow_six_mem_centralizer_of_thompsonJ hCT (uc22p22e_solvable_autOn D hsolv) hT hV x hx

theorem uc22p22e_jOf_M_le_centralizer (D : Data G) (h : jOf D.T ≤ centralizer (D.U : Set G)) :
    jOf D.M ≤ centralizer (D.U : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ∀ S : Subgroup G, jOf S = CFSG.Quasithin.thompsonJ S := fun S =>
    CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ S
  have hV : D.M ≤ normalizer (D.U : Set G) := le_normalizer_uCore D.M D.T
  rw [h1] at h ⊢
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAM, hAel, hAmax⟩ := hA
  obtain ⟨k, hk, hkA⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.exists_conj_le_of_isSylowOf
    D.sylowM hAM (uc22p22e_isPGroup_of_elem hAel)
  have hA'T : A.map (MulAut.conj k⁻¹).toMonoidHom ≤ D.T := by
    rintro _ ⟨x, hx, rfl⟩
    have := hkA x hx
    simpa using this
  have hA'max : CFSG.Quasithin.IsMaxElemAbelian D.T (A.map (MulAut.conj k⁻¹).toMonoidHom) := by
    refine ⟨hA'T, uc22p22e_isElemAbelian_map hAel _, fun B hBT hBel => ?_⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective]
    exact hAmax B (hBT.trans D.sylowM.le) hBel
  have hA'J : A.map (MulAut.conj k⁻¹).toMonoidHom ≤ CFSG.Quasithin.thompsonJ D.T :=
    le_iSup₂_of_le _ hA'max le_rfl
  intro x hx
  have hxk : k⁻¹ * x * k ∈ A.map (MulAut.conj k⁻¹).toMonoidHom := ⟨x, hx, by simp⟩
  have hc := Subgroup.mem_centralizer_iff.1 (h (hA'J hxk))
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : k⁻¹ * u * k ∈ D.U := by
    have := uc22br_gt_conj_mem hV (D.M.inv_mem hk) hu
    simpa using this
  have h2 := hc _ hu'
  have h3 := congrArg (fun y => k * y * k⁻¹) h2
  simpa [mul_assoc] using h3

theorem uc22p22e_main613 (D : Data G) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hker : D.M ⊓ centralizer (D.U : Set G) = pCoreOf 2 D.M) (hsolv : Group.IsSolvable ↥D.M)
    {Q₁ : Subgroup G} (hQp : IsPGroup p Q₁) (hQM : Q₁ ≤ D.M)
    (hnorm : D.M ≤ normalizer ((Q₁ ⊔ pCoreOf 2 D.M : Subgroup G) : Set G))
    (hfaith : ∀ t ∈ D.T, (∀ x ∈ Q₁, t * x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 D.M) → t ∈ pCoreOf 2 D.M) :
    jOf D.M ≤ centralizer (D.U : Set G) := by
  have hV : D.M ≤ normalizer (D.U : Set G) := le_normalizer_uCore D.M D.T
  have hOM : pCoreOf 2 D.M ≤ D.M := Subgroup.map_subtype_le _
  have hOC : pCoreOf 2 D.M ≤ centralizer (D.U : Set G) := hker ▸ inf_le_right
  have h6 := uc22p22e_pow_six D hsolv
  have hJM : D.M ≤ normalizer (jOf D.M : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact uc22p22e_conj_jOf (fun x hx => D.M.mul_mem (D.M.mul_mem hy
        (uc22p22e_jOf_le_self D.M hx)) (D.M.inv_mem hy)) x hx
    · intro hx
      have := uc22p22e_conj_jOf (T := D.M) (y := y⁻¹) (fun x hx => D.M.mul_mem
        (D.M.mul_mem (D.M.inv_mem hy) (uc22p22e_jOf_le_self D.M hx)) (D.M.inv_mem (D.M.inv_mem hy)))
        _ hx
      simpa [mul_assoc] using this
  have hbot : mbarImage D.M D.U (pCoreOf 2 D.M) = ⊥ :=
    (uc22br4_mbarImage_eq_bot_iff D.M D.U _ hV hOM).2 hOC
  have hQbar : mbarImage D.M D.U (Q₁ ⊔ pCoreOf 2 D.M) = mbarImage D.M D.U Q₁ := by
    unfold mbarImage at hbot ⊢
    rw [Subgroup.subgroupOf_sup hQM hOM, Subgroup.map_sup, hbot, sup_bot_eq]
  haveI hQn : (mbarImage D.M D.U Q₁).Normal := by
    rw [← hQbar]
    exact uc22br4_mbarImage_normal D.M D.U _ (sup_le hQM hOM) hnorm
  haveI hNn : (mbarImage D.M D.U (jOf D.M)).Normal :=
    uc22br4_mbarImage_normal D.M D.U _ (uc22p22e_jOf_le_self D.M) hJM
  have hcomm : ∀ t ∈ jOf D.M, ∀ z ∈ Q₁, t * z * t⁻¹ * z⁻¹ ∈ centralizer (D.U : Set G) := by
    intro t ht z hz
    have htM : t ∈ D.M := uc22p22e_jOf_le_self D.M ht
    have hzM : z ∈ D.M := hQM hz
    let tm : ↥D.M := ⟨t, htM⟩
    let zm : ↥D.M := ⟨z, hzM⟩
    let tb : MBar D.M D.U := QuotientGroup.mk tm
    let zb : MBar D.M D.U := QuotientGroup.mk zm
    have htbar : tb ∈ mbarImage D.M D.U (jOf D.M) := ⟨tm, ht, rfl⟩
    have hzbar : zb ∈ mbarImage D.M D.U Q₁ := ⟨zm, hz, rfl⟩
    have hc := Subgroup.commutator_mem_commutator htbar hzbar
    have hc2 := Subgroup.commutator_le_inf (mbarImage D.M D.U (jOf D.M)) (mbarImage D.M D.U Q₁) hc
    obtain ⟨hcN, hcQ⟩ := Subgroup.mem_inf.1 hc2
    obtain ⟨c, hcdef⟩ : ∃ c : MBar D.M D.U, c = ⁅tb, zb⁆ := ⟨_, rfl⟩
    rw [← hcdef] at hcN hcQ
    have hc6 : c ^ 6 = 1 := by
      obtain ⟨a, ha, hac⟩ := hcN
      have hac' : (QuotientGroup.mk a : MBar D.M D.U) = c := hac
      rw [← hac', ← QuotientGroup.mk_pow, uc22br_gt_mk_eq_one_iff hV]
      have := h6 (a : G) ha
      simpa using this
    obtain ⟨k, hck⟩ : ∃ k : ℕ, c ^ (p ^ k) = 1 := by
      obtain ⟨b, hb, hbc⟩ := hcQ
      have hbc' : (QuotientGroup.mk b : MBar D.M D.U) = c := hbc
      obtain ⟨k, hk⟩ := hQp ⟨(b : G), hb⟩
      refine ⟨k, ?_⟩
      rw [← hbc', ← QuotientGroup.mk_pow]
      have : b ^ (p ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, QuotientGroup.mk_one]
    have hcop : Nat.Coprime 6 (p ^ k) := by
      refine Nat.Coprime.pow_right _ ?_
      exact Nat.Coprime.mul_left ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))
        ((Nat.coprime_primes Nat.prime_three hp).2 (by omega))
    have hc1 : c = 1 := by
      have h1 : orderOf c ∣ Nat.gcd 6 (p ^ k) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc6) (orderOf_dvd_of_pow_eq_one hck)
      rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
      exact h1
    have h1 : (QuotientGroup.mk (tm * zm * tm⁻¹ * zm⁻¹) : MBar D.M D.U) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv]
      rw [commutatorElement_def] at hcdef
      rw [← hcdef]
      exact hc1
    have h2 := (uc22br_gt_mk_eq_one_iff hV (tm * zm * tm⁻¹ * zm⁻¹)).1 h1
    simpa using h2
  have hJT : jOf D.T ≤ centralizer (D.U : Set G) := by
    intro t ht
    have htT : t ∈ D.T := uc22p22e_jOf_le_self D.T ht
    have htJ : t ∈ jOf D.M := uc22p22e_jOf_le D.sylowM ht
    have htM : t ∈ D.M := D.sylowM.le htT
    have hO : t ∈ pCoreOf 2 D.M := hfaith t htT (fun x hx => by
      rw [← hker]
      exact ⟨D.M.mul_mem (D.M.mul_mem (D.M.mul_mem htM (hQM hx)) (D.M.inv_mem htM))
        (D.M.inv_mem (hQM hx)), hcomm t htJ x hx⟩)
    exact hOC hO
  exact uc22p22e_jOf_M_le_centralizer D hJT

theorem uc22p22e_false_of_613 (D : Data G) (Ch : Choice2011 G) (h121 : S22_1 D Ch)
    (h3_1 : S22_3_1 D Ch) (hhyp612 : ∀ p ∈ D.sig2, ∃ P P₀ : Subgroup G, UC6.Hyp612 D p P P₀)
    (h613 : UC6.R6_13 D) (h1930 : H1930 D) (c : Ctx22c D Ch) {p : ℕ} (hp : p ∈ D.sig2) : False := by
  obtain ⟨hpP, _⟩ := D.sig_prime p (by rw [D.sig_sub]; exact Or.inl (Or.inr hp))
  have hker := (h121 h1930 c.toCtx22).2 ⟨p, hp⟩
  obtain ⟨P, P₀, hP⟩ := hhyp612 p hp
  have h613' := h613 p P P₀ hP
  have hQp : IsPGroup p ↥(P ⊓ UC6.inftyOf (centralizer (P₀ : Set G))) :=
    hP.sylow.isPGroup.to_le inf_le_left
  have hJ := uc22p22e_main613 D hpP h613'.1.1 hker h613'.1.2.1 hQp (inf_le_left.trans hP.sylow.le)
    h613'.2.2.2.1.2.1 h613'.2.2.2.1.2.2
  exact (h3_1 h1930 c).1 ((uc22br4_mbarImage_eq_bot_iff D.M D.U (proofN D)
    (le_normalizer_uCore D.M D.T) (uc22p22e_jOf_le_self D.M)).2 hJ)

theorem s22_4_of' (D : Data G) (Ch : Choice2011 G) (h121 : S22_1 D Ch) (h3_1 : S22_3_1 D Ch)
    (hhyp612 : ∀ p ∈ D.sig2, ∃ P P₀ : Subgroup G, UC6.Hyp612 D p P P₀) (h613 : UC6.R6_13 D) :
    S22_4 D Ch := by
  intro h1930 c
  have hsig3 := (h121 h1930 c.toCtx22).1
  refine Set.Subset.antisymm (fun p hp => ?_) (fun p hp => ?_)
  · have hp' := hp
    rw [D.sig_sub] at hp'
    rcases hp' with (h | h) | h
    · exact h
    · exact (uc22p22e_false_of_613 D Ch h121 h3_1 hhyp612 h613 h1930 c h).elim
    · rw [hsig3] at h
      exact (Set.notMem_empty p h).elim
  · rw [D.sig_sub]
    exact Or.inl (Or.inl hp)

end CFSG.LocalAnalysis.UniquenessCase.UC22
