module

public import CFSG.RankThree.PartTwo.Sec19.Step1919CoreDefs
public import CFSG.RankThree.PartTwo.Sec19.Step1919CoreGL
public import CFSG.RankThree.PartTwo.Sec19.Step1919CoreOrbit
import CFSG.RankThree.PartTwo.KFacts.KS14GL33
import CFSG.RankThree.PartTwo.Sec18.Transport
public import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowTools

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec18

namespace Step1919CoreProof

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_of_mem_autIn {N E : Subgroup G} {σ : MulAut E} (hσ : σ ∈ Sec4.autIn N E)
    (hσ3 : ∃ k : ℕ, σ ^ 3 ^ k = 1) :
    ∃ (z : G) (hzE : z ∈ Subgroup.normalizer (E : Set G)), z ∈ N ∧ (∃ a : ℕ, z ^ 3 ^ a = 1) ∧
      E.normalizerMonoidHom ⟨z, hzE⟩ = σ := by
  obtain ⟨g, hgE, hgN, hgσ⟩ := Sec4.mem_autIn_iff.mp hσ
  obtain ⟨a, m, hm3, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  have hy3 : (g ^ m) ^ 3 ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  obtain ⟨k, hk⟩ := hσ3
  have hcop : Nat.Coprime m (orderOf σ) :=
    (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3)).symm
      |>.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk)
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
  have hzE : (g ^ m) ^ n ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.pow_mem _ (Subgroup.pow_mem _ hgE m) n
  refine ⟨(g ^ m) ^ n, hzE, Subgroup.pow_mem _ (Subgroup.pow_mem _ hgN m) n,
    ⟨a, by rw [← pow_mul, mul_comm, pow_mul, hy3, one_pow]⟩, ?_⟩
  have e : (⟨(g ^ m) ^ n, hzE⟩ : Subgroup.normalizer (E : Set G)) =
      ((⟨g, hgE⟩ : Subgroup.normalizer (E : Set G)) ^ m) ^ n := Subtype.ext (by simp)
  rw [e, map_pow, map_pow, hgσ, hn]

theorem exists_transvection (hK : KFacts.KS18GL33) {A L E M : Subgroup G} {c : G}
    (hctx : Ctx1912 G A c L E M) (h9 : Nat.card (E ⊓ L : Subgroup G) = 9)
    (hX : Sec4.IsExtOf
      (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) E))
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    ∃ u : G, u ∈ Subgroup.normalizer (E : Set G) ∧
      u ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) ∧ (∃ a : ℕ, u ^ 3 ^ a = 1) ∧
      (∀ f ∈ E ⊓ L, u * f * u⁻¹ = f) ∧ c * u ≠ u * c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set F := E ⊓ L with hFdef
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hFE : F ≤ E := inf_le_left
  have hcA : c ∈ A := hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)
  have hcE : c ∈ E :=
    mem_of_le_centralizer hctx.toPartTwoStanding hctx.partTwoS_eq hEE
      (hctx.mem_partTwoE.1.2 c hcA) hctx.le_centralizer
  have hcL : c ∉ L := hctx.hypS.2.2 c hctx.zpowers_mem_omegaA L hctx.mem_lA
  set X := oUpperThreePrime (Sec4.autIn (Subgroup.normalizer (F : Set G)) E) with hXdef
  have hXle : X ≤ Sec4.autIn (Subgroup.normalizer (F : Set G)) E := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro σ ⟨hσ, -⟩
    exact hσ
  have hF'9 : Nat.card (F.subgroupOf E) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv]
    exact h9
  have hEab : CFSG.Assembly.IsElemAbelian 3 (⊤ : Subgroup E) := by
    have := (isE27_subgroupOf hE le_rfl).1
    rwa [Subgroup.subgroupOf_self] at this
  have hstab : ∀ σ ∈ X, (F.subgroupOf E).map σ.toMonoidHom = F.subgroupOf E := by
    intro σ hσ
    obtain ⟨g, hgN, hgF, hgσ⟩ := Sec4.mem_autIn_iff.mp (hXle hσ)
    refine Subgroup.eq_of_le_of_card_ge ?_
      (by rw [Subgroup.card_map_of_injective σ.injective])
    rintro _ ⟨x, hx, rfl⟩
    change x ∈ F.subgroupOf E at hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [← hgσ]
    change ((E.normalizerMonoidHom ⟨g, hgN⟩ x : E) : G) ∈ F
    rw [Sec4.normalizerMonoidHom_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp hgF _).mp hx
  obtain ⟨σ, hσX, hσF, hσE, hσmove⟩ := hK E hEab hE.2 (F.subgroupOf E) hF'9 X hstab hX
  obtain ⟨g, hgN, hgF, hgσ⟩ := Sec4.mem_autIn_iff.mp (hXle hσX)
  obtain ⟨a, m, hm3, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  set y := g ^ m with hy
  have hy3 : y ^ (3 ^ a) = 1 := by
    rw [hy, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hyN : y ∈ Subgroup.normalizer (E : Set G) := Subgroup.pow_mem _ hgN m
  have hyF : y ∈ Subgroup.normalizer (F : Set G) := Subgroup.pow_mem _ hgF m
  have hyσ : E.normalizerMonoidHom ⟨y, hyN⟩ = σ ^ m := by
    rw [← hgσ, ← map_pow]
    congr 1
  have hyact : ∀ e (he : e ∈ E), y * e * y⁻¹ = ((σ ^ m) ⟨e, he⟩ : G) := by
    intro e he
    rw [← hyσ, Sec4.normalizerMonoidHom_apply_coe]
  have hyFfix : ∀ f ∈ F, y * f * y⁻¹ = f := by
    intro f hf
    rw [hyact f (hFE hf), pow_apply_of_transvection hσF hσE,
      hσF ⟨f, hFE hf⟩ (Subgroup.mem_subgroupOf.mpr hf)]
    simp
  have hcy : c * y ≠ y * c := by
    intro hcomm
    have hc' : (⟨c, hcE⟩ : E) ∉ F.subgroupOf E := by
      rw [Subgroup.mem_subgroupOf]
      exact fun h => hcL h.2
    have hmove := hσmove _ hc'
    obtain ⟨w, hw⟩ : ∃ w : E, w = σ ⟨c, hcE⟩ * (⟨c, hcE⟩ : E)⁻¹ := ⟨_, rfl⟩
    have hw1 : w ≠ 1 := fun h => hmove (by rw [← mul_inv_eq_one, ← hw]; exact h)
    have hw3 : w ^ 3 = 1 := Subtype.ext (by simpa using hE.1.2 _ w.2)
    have hwm : w ^ m ≠ 1 := by
      intro h
      have hd : orderOf w ∣ Nat.gcd 3 m :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hw3) (orderOf_dvd_of_pow_eq_one h)
      rw [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3),
        Nat.dvd_one, orderOf_eq_one_iff] at hd
      exact hw1 hd
    apply hwm
    have h1 := hyact c hcE
    rw [pow_apply_of_transvection hσF hσE, ← hw] at h1
    have h2 : y * c * y⁻¹ = c := by
      rw [← hcomm]
      group
    rw [h2] at h1
    apply Subtype.ext
    simp only [Subgroup.coe_mul] at h1
    simpa using h1
  exact ⟨y, hyN, hyF, ⟨a, hy3⟩, hyFfix, hcy⟩

theorem mem_normalizer_of_mem_scriptJ
    {A L E M H J : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    (h9 : Nat.card (E ⊓ L : Subgroup G) = 9)
    (hX : Sec4.IsExtOf
      (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) E))
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (hH : H ∈ scriptM (Subgroup.centralizer ({c} : Set G) : Set G)) (hJ : J ∈ scriptJ M H)
    (hlist : IsList194 (J ⧸ CFSG.pCore 2 J) ∨ IsSmall194 (J ⧸ CFSG.pCore 2 J))
    (hpar : (IsEmpty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
        IsProperParabolic (starIm J H)) ∨
      (Nonempty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
        Sec4.IsExtOf (starIm J H) (Equiv.Perm (Fin 5)) (Multiplicative (Fin 4 → ZMod 2))))
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) :
    ∀ g ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) ⊓
        Subgroup.normalizer (E : Set G),
      (∃ k : ℕ, g ^ 3 ^ k = 1) → g ∈ Subgroup.normalizer (J : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEe : ∀ e ∈ E, e ^ 3 = 1 := hE.1.2
  have hEH : E ≤ H := fun x hx => hH.2 (hctx.le_centralizer hx)
  have hFE : E ⊓ L ≤ E := inf_le_left
  have hFN : Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) ≤ M :=
    (normalizer_le_gamma hFE (two_le_pRank_of_elemAbelian (isElemAbelian_of_le hE.1 hFE)
      h9.ge)).trans hctx.mem_scriptM.2
  have hJM : J ∈ oTwoComponentsIn M := hJ.1
  obtain ⟨y, hy3, hyc, hync⟩ := Step1919NarrowTools.exists_fixed_noncentral hJM hlist hpar
    hE.isPGroup hEe hEJ hEH
  have hyE : (y : G) ∈ E := mem_of_le_centralizer hctx.toPartTwoStanding hctx.partTwoS_eq hEE
    hy3 fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hyc a ha)
  have hyn := Step1919Narrow.exists_not_mem_of_not_mem_center hJM y hync
  obtain ⟨u, huE, huF, hu3, hufix, hcu⟩ := exists_transvection KFacts.KS14.ks18GL33 hctx h9 hX
  have hcE : c ∈ E :=
    mem_of_le_centralizer hctx.toPartTwoStanding hctx.partTwoS_eq hEE
      (hctx.mem_partTwoE.1.2 c (hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)))
      hctx.le_centralizer
  have hue : ∃ e ∈ E, u * e * u⁻¹ ≠ e := ⟨c, hcE, fun h => hcu (by
    calc c * u = u * c * u⁻¹ * u := by rw [h]
      _ = u * c := by group)⟩
  exact fun g hg hg3 =>
    mem_normalizer_of_pow hEc hEe hE.2 hFE h9 hJM hyE y.2 hyn (hFN huF) huE hu3 hufix hue
      (hFN hg.1) hg.2 hg3

theorem eq_or_eq_of_conj_mem {A L E M : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    (h9 : Nat.card (E ⊓ L : Subgroup G) = 9)
    (hX : Sec4.IsExtOf
      (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) E))
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    {V : Subgroup G} (hVE : V ≤ E) (hV1 : V ≠ ⊥)
    (hV : ∀ z ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) ⊓
        Subgroup.normalizer (E : Set G), (∃ k : ℕ, z ^ 3 ^ k = 1) →
      ∀ v ∈ V, z * v * z⁻¹ ∈ V) :
    V = E ⊓ L ∨ V = E := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEe : ∀ e ∈ E, e ^ 3 = 1 := hE.1.2
  set F := E ⊓ L with hFdef
  have hFE : F ≤ E := inf_le_left
  set S : Set (MulAut E) := {σ | σ ∈ Sec4.autIn (Subgroup.normalizer (F : Set G)) E ∧
    ∃ k : ℕ, σ ^ 3 ^ k = 1} with hSdef
  have hVc : ∀ a b : E, a * b = b * a := fun a b => Subtype.ext (hEc a a.2 b b.2)
  have hVe : ∀ v : E, v ^ 3 = 1 := fun v => Subtype.ext (by simpa using hEe v v.2)
  have hF'9 : Nat.card (F.subgroupOf E) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv]
    exact h9
  have hS3 : ∀ σ ∈ S, ∃ k : ℕ, σ ^ 3 ^ k = 1 := fun σ hσ => hσ.2
  have hSF : ∀ σ ∈ S, ∀ f ∈ F.subgroupOf E, σ f ∈ F.subgroupOf E := by
    intro σ hσ f hf
    obtain ⟨g, hgN, hgF, hgσ⟩ := Sec4.mem_autIn_iff.mp hσ.1
    rw [Subgroup.mem_subgroupOf] at hf ⊢
    rw [← hgσ, Sec4.normalizerMonoidHom_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp hgF _).mp hf
  have hSW : ∀ σ ∈ S, ∀ w ∈ V.subgroupOf E, σ w ∈ V.subgroupOf E := by
    intro σ hσ w hw
    obtain ⟨z, hzE, hzF, hz3, hzσ⟩ := exists_pow_of_mem_autIn hσ.1 hσ.2
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    rw [← hzσ, Sec4.normalizerMonoidHom_apply_coe]
    exact hV z ⟨hzF, hzE⟩ hz3 _ hw
  have hX216 : 81 < Nat.card (Subgroup.closure S) := by
    obtain ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ := hX
    have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
      rw [Nat.card_eq_fintype_card]
      decide
    have hcard : Nat.card (oUpperThreePrime
        (Sec4.autIn (Subgroup.normalizer (F : Set G)) E)) = 216 := by
      rw [N.card_eq_card_quotient_mul_card_subgroup, Nat.card_congr eQ.toEquiv,
        Nat.card_congr eN.toEquiv, Nat.card_prod, hSL]
      simp
    change 81 < Nat.card (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer (F : Set G)) E))
    rw [hcard]
    norm_num
  have hW1 : V.subgroupOf E ≠ ⊥ := by
    intro h
    apply hV1
    rw [eq_bot_iff]
    intro v hv
    have hmem : (⟨v, hVE hv⟩ : E) ∈ V.subgroupOf E := Subgroup.mem_subgroupOf.mpr hv
    rw [h, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hmem)
  rcases eq_or_eq_top_of_invariant hVc hVe hE.2 hF'9 hS3 hSF hX216 hSW hW1 with h | h
  · left
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hVE, inf_eq_left.mpr hFE] at h
    exact h
  · right
    rw [Subgroup.subgroupOf_eq_top] at h
    exact le_antisymm hVE h

theorem inf_eq_or_le_of_mem_scriptJ
    {A L E M H J : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    (h9 : Nat.card (E ⊓ L : Subgroup G) = 9)
    (hX : Sec4.IsExtOf
      (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) E))
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (hH : H ∈ scriptM (Subgroup.centralizer ({c} : Set G) : Set G)) (hJ : J ∈ scriptJ M H)
    (hlist : IsList194 (J ⧸ CFSG.pCore 2 J) ∨ IsSmall194 (J ⧸ CFSG.pCore 2 J))
    (hpar : (IsEmpty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
        IsProperParabolic (starIm J H)) ∨
      (Nonempty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
        Sec4.IsExtOf (starIm J H) (Equiv.Perm (Fin 5)) (Multiplicative (Fin 4 → ZMod 2))))
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) : E ⊓ J = E ⊓ L ∨ E ≤ J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hEe : ∀ e ∈ E, e ^ 3 = 1 := hE.1.2
  have hEH : E ≤ H := fun x hx => hH.2 (hctx.le_centralizer hx)
  have hJM : J ∈ oTwoComponentsIn M := hJ.1
  have hP3 := mem_normalizer_of_mem_scriptJ hctx h9 hX hH hJ hlist hpar hEJ
  obtain ⟨y, hy3, hyc, hync⟩ := Step1919NarrowTools.exists_fixed_noncentral hJM hlist hpar
    hE.isPGroup hEe hEJ hEH
  have hyE : (y : G) ∈ E := mem_of_le_centralizer hctx.toPartTwoStanding hctx.partTwoS_eq hEE
    hy3 fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hyc a ha)
  have hyn := Step1919Narrow.exists_not_mem_of_not_mem_center hJM y hync
  have hy1 : (y : G) ≠ 1 := fun h => not_mem_cenMod hyn (h ▸ Subgroup.one_mem _)
  have hV1 : E ⊓ J ≠ ⊥ := fun h => hy1 ((Subgroup.mem_bot).mp (h ▸ ⟨hyE, y.2⟩))
  rcases eq_or_eq_of_conj_mem hctx h9 hX inf_le_left hV1 (fun z hz hz3 v hv =>
    ⟨(Subgroup.mem_normalizer_iff.mp hz.2 v).mp hv.1,
      (Subgroup.mem_normalizer_iff.mp (hP3 z hz hz3) v).mp hv.2⟩) with h | h
  · exact Or.inl h
  · exact Or.inr (h ▸ inf_le_right)

end Step1919CoreProof

open Step1919CoreProof in
theorem step1919Core_of
    (hsplit : Step1919CoreSplit) : Step1919Core := by
  intro G _ _ A c L E M hctx hLM h9 hX H hH hHM hne hJall hEN hcJ
  obtain ⟨J, hJ⟩ := hne
  obtain ⟨hlist, hpar⟩ := hJall J hJ
  refine ⟨J, hJ, ?_⟩
  rcases inf_eq_or_le_of_mem_scriptJ hctx h9 hX hH hJ hlist hpar (hEN J hJ) with h | h
  · exact absurd h (hsplit G A c L E M hctx hLM h9 hX H hH hHM hJall hEN hcJ J hJ
      (mem_normalizer_of_mem_scriptJ hctx h9 hX hH hJ hlist hpar (hEN J hJ)))
  · exact h

end CFSG.RankThree.PartTwo.Sec19
