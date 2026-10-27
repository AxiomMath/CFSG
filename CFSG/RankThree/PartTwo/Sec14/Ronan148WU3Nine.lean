module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WU3RankOf
import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofTools
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.ClassicalInvolution.Sp62Rec.FourLift
import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

@[expose] def KF148FieldE27 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ) [Fact p.Prime], 1 ≤ f → Sec4.IsoLThreePi X p f →
    (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8) → ¬ (p = 2 ∧ p ^ f % 9 = 8) →
    ∀ E : Subgroup (MulAut X), CFSG.Open.IsElemAbelian 3 E → Nat.card E = 27 →
      ∃ B : Subgroup (MulAut X), B ≤ E ∧ Nat.card B = 9 ∧
        ∃ T : Subgroup X, T ≠ ⊥ ∧ IsPGroup 2 T ∧ ∀ b ∈ B, ∀ t ∈ T, (b : MulAut X) t ∈ T

@[expose] def Step148OmegaRankThreeNineU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ e ∈ A, Subgroup.zpowers e ∈ omegaA A → ∀ Le ∈ lA A e,
    ∀ f : ℕ, 1 ≤ f → ∀ _ : Fact (Nat.Prime 2),
      Sec4.IsoLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) 2 f → 2 ^ f % 9 = 8 →
      ∀ F : Subgroup G, e ∈ F → CFSG.Open.IsElemAbelian 3 F → Nat.card F = 81 →
        F ⊓ Sec4.thetaQuotCentralizer Le ≤ Subgroup.zpowers e → False

variable {G : Type} [Group G] [Finite G]

theorem card_comap_of_le_range {X Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y)
    {K : Subgroup Y} (hK : K ≤ f.range) :
    Nat.card (K.comap f) = Nat.card K * Nat.card f.ker := by
  set g := f.comp (K.comap f).subtype with hg
  have hrange : g.range = K := by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := hK hy
      exact ⟨⟨x, hy⟩, rfl⟩
  have hle : f.ker ≤ K.comap f := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact K.one_mem
  have hker : g.ker = f.ker.subgroupOf (K.comap f) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]

theorem exists_two_subgroup_of_preserves {L F₀ : Subgroup G}
    (hF₀N : F₀ ≤ Subgroup.normalizer (L : Set G)) (hF₀ : IsPGroup 3 F₀)
    {T : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hpres : ∀ (x : G) (hx : x ∈ F₀), ∀ t ∈ T,
      Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨x, hF₀N hx⟩) t ∈ T) :
    ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 S ∧ F₀ ≤ Subgroup.normalizer (S : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set Tt : Subgroup G := (T.comap (QuotientGroup.mk' θ)).map L.subtype with hTt
  have hcard : Nat.card Tt = Nat.card T * Nat.card θ := by
    rw [hTt, Subgroup.card_map_of_injective L.subtype_injective,
      CFSG.ClassicalInvolution.Sp62Rec.natCard_comap_mk]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
  have hk1 : 1 ≤ k := by
    by_contra h
    push Not at h
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero] at hk
    exact hT (Subgroup.eq_bot_of_card_eq T hk)
  have h3 : ¬ 3 ∣ Nat.card Tt := by
    rw [hcard, hk]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    · exact three_not_dvd_card_aschbacherSolvableCore h
  have h2 : 2 ∣ Nat.card Tt := by
    rw [hcard, hk]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have hF₀T : F₀ ≤ Subgroup.normalizer (Tt : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨l, hl, rfl⟩ := hy
    have hmem : (L.normalizerMonoidHom ⟨x, hF₀N hx⟩ l : ↥L) ∈ T.comap (QuotientGroup.mk' θ) := by
      rw [Subgroup.mem_comap]
      exact hpres x hx _ (Subgroup.mem_comap.mp hl)
    refine ⟨_, hmem, ?_⟩
    rw [Subgroup.coe_subtype, Sec4.coe_normalizerMonoidHom]
    rfl
  obtain ⟨R, -, hR2, hF₀R, hRcard⟩ :=
    Sec17.HeadProof.exists_invariant_sylow hF₀ h3 hF₀T Nat.prime_two
  refine ⟨R, ?_, hR2, hF₀R⟩
  intro hR
  rw [hR, Subgroup.card_bot] at hRcard
  have hfac : 1 ≤ (Nat.card Tt).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
  have : 2 ≤ 2 ^ (Nat.card Tt).factorization 2 :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (Nat.card Tt).factorization 2 := Nat.pow_le_pow_right (by norm_num) hfac
  omega

theorem step148OmegaRankThreeNine_of (hKF : KF148FieldE27) (hU : Step148OmegaRankThreeNineU) :
    Step148OmegaRankThreeNine := by
  intro G _ _ A c L h e he heΩ Le hLeA p f hp hf hiso h9 F heF hF hF81 hP
  by_cases hbad : p = 2 ∧ p ^ f % 9 = 8
  · obtain ⟨rfl, h8⟩ := hbad
    exact hU G A c L h e he heΩ Le hLeA f hf hp hiso h8 F heF hF hF81 hP
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := h.mem_partTwoF.1.2
  have he3 : e ^ 3 = 1 := hA3 e he
  have he1 : e ≠ 1 := by
    intro h1
    obtain ⟨-, hcard, -⟩ := heΩ
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hLeC : Le ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLeA.1
  have h3 : 3 ∣ Nat.card Le :=
    (Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi hf hiso).trans
      (Subgroup.card_quotient_dvd_card _)
  have hFC : F ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨e, heF⟩))
  have hFN : F ≤ Subgroup.normalizer (Le : Set G) :=
    hFC.trans (Proof1413Res3.centralizer_le_normalizer_of_mem_lA h heΩ hLeA h3)
  have heN : e ∈ Subgroup.normalizer (Le : Set G) := hFN heF
  set φ := (Sec4.thetaQuotMulAut ↥Le).comp Le.normalizerMonoidHom with hφ
  set F' := F.subgroupOf (Subgroup.normalizer (Le : Set G)) with hF'
  set ψ := φ.comp F'.subtype with hψ
  have hF'card : Nat.card F' = 81 := by
    rw [hF', ← hF81]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv
  have hF'ab : CFSG.Open.IsElemAbelian 3 F' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => Subtype.ext ?_⟩
    · exact (show ((a : Subgroup.normalizer (Le : Set G)) : G) * b = b * a from
        congrArg Subtype.val (hF.1.is_comm.comm ⟨_, Subgroup.mem_subgroupOf.mp a.2⟩
          ⟨_, Subgroup.mem_subgroupOf.mp b.2⟩))
    · exact hF.2 _ (Subgroup.mem_subgroupOf.mp hy)
  have hmem : ∀ x : ψ.ker, (((x : F') : Subgroup.normalizer (Le : Set G)) : G) ∈
      Subgroup.zpowers e := by
    intro x
    apply hP
    refine ⟨Subgroup.mem_subgroupOf.mp (x : F').2, ⟨(x : F'), ?_, rfl⟩⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact MonoidHom.mem_ker.mp x.2
  have hker3 : Nat.card ψ.ker ≤ 3 := by
    calc Nat.card ψ.ker ≤ Nat.card (Subgroup.zpowers e) :=
          Nat.card_le_card_of_injective (fun x => ⟨_, hmem x⟩) (by
            intro x y hxy
            have h1 := congrArg (fun z : Subgroup.zpowers e => (z : G)) hxy
            simp only at h1
            exact Subtype.ext (Subtype.ext (Subtype.ext h1)))
      _ ≤ 3 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one he3)
  have hnm : Le.normalizerMonoidHom ⟨e, heN⟩ = 1 := by
    refine MulEquiv.ext fun l => Subtype.ext ?_
    rw [Sec4.coe_normalizerMonoidHom, MulAut.one_apply]
    show e * (l : G) * e⁻¹ = l
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hLeC l.2)).symm, mul_inv_cancel_right]
  set e' : F' := ⟨⟨e, heN⟩, Subgroup.mem_subgroupOf.mpr heF⟩ with he'def
  have he'k : e' ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    show (Sec4.thetaQuotMulAut ↥Le) (Le.normalizerMonoidHom ⟨e, heN⟩) = 1
    rw [hnm, map_one]
  have he'3 : e' ^ 3 = 1 := Subtype.ext (Subtype.ext he3)
  have he'1 : e' ≠ 1 := fun h1 => he1 (congrArg Subtype.val (congrArg Subtype.val h1))
  have hker3' : 3 ≤ Nat.card ψ.ker := by
    calc 3 = Nat.card (Subgroup.zpowers e') := by
          rw [Nat.card_zpowers, orderOf_eq_prime he'3 he'1]
      _ ≤ Nat.card ψ.ker := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr he'k)
  have hkerc : Nat.card ψ.ker = 3 := le_antisymm hker3 hker3'
  have hcard : Nat.card F' = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, mul_comm]
  have hrange27 : Nat.card ψ.range = 27 := by
    rw [hF'card, hkerc] at hcard
    omega
  have hrangeab : CFSG.Open.IsElemAbelian 3 ψ.range := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
    exact isElemAbelian_map _ hF'ab
  obtain ⟨B, hBE, hB9, T, hT, hT2, hBT⟩ := hKF _ p f hf hiso h9 hbad ψ.range hrangeab hrange27
  set F₀' := B.comap ψ with hF₀'
  have hF₀'card : Nat.card F₀' = 27 := by
    rw [hF₀', card_comap_of_le_range ψ hBE, hB9, hkerc]
  set F₀ : Subgroup G := (F₀'.map F'.subtype).map (Subgroup.normalizer (Le : Set G)).subtype
    with hF₀
  have hF₀card : Nat.card F₀ = 27 := by
    rw [hF₀, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hF₀'card]
  have hF₀F : F₀ ≤ F := by
    rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.mp y.2
  have hF₀N : F₀ ≤ Subgroup.normalizer (Le : Set G) := hF₀F.trans hFN
  have hF₀3 : IsPGroup 3 F₀ := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one]; exact hF.2 _ (hF₀F g.2))⟩
  have hpres : ∀ (x : G) (hx : x ∈ F₀), ∀ t ∈ T,
      Sec4.thetaQuotMulAut ↥Le (Le.normalizerMonoidHom ⟨x, hF₀N hx⟩) t ∈ T := by
    intro x hx t ht
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hx
    exact hBT _ hy t ht
  obtain ⟨S, hS, hS2, hF₀S⟩ := exists_two_subgroup_of_preserves hF₀N hF₀3 hT hT2 hpres
  have hF₀ab : CFSG.Assembly.IsElemAbelian 3 F₀ :=
    ⟨⟨⟨fun a b => Subtype.ext (show (a : G) * b = b * a from congrArg Subtype.val
      (hF.1.is_comm.comm ⟨a, hF₀F a.2⟩ ⟨b, hF₀F b.2⟩))⟩⟩, fun y hy => hF.2 y (hF₀F hy)⟩
  have hF₀E : F₀ ∈ partTwoE G := ⟨hF₀ab, hF₀card, S, hS, hS2, hF₀S⟩
  have hF₀F' : F₀ ∈ partTwoF G := by
    rw [(h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1]
    exact hF₀E
  have heq := hF₀F'.2.1 F hF hF₀F
  rw [heq, hF₀card] at hF81
  omega

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
