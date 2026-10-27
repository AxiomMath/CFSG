module

public import CFSG.Quasithin.Background.F6CatRecogTools
public import CFSG.CharacterTheory.Wreathed.LocalOddCorePerfectNormalizer
public import CFSG.Quasithin.Background.F6CatSetting

public section

namespace CFSG.Quasithin

namespace F6

section SettingSylow

abbrev TwoResidualQuot (D : Type) [Group D] : Type :=
  ↥(twoResidual (⊤ : Subgroup D)) ⧸ Subgroup.center ↥(twoResidual (⊤ : Subgroup D))

theorem exists_index_twoResidual_eq {D : Type} [Group D] [Finite D] :
    ∃ n : ℕ, (twoResidual (⊤ : Subgroup D)).index = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := twoResidual_top_normal (D := D)
  have hp : IsPGroup 2 (D ⧸ twoResidual (⊤ : Subgroup D)) := fun q => by
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup D) y (Subgroup.mem_top y)
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  exact ⟨n, by rw [Subgroup.index_eq_card, hn]⟩

variable {D : Type} [Group D] [Finite D]

@[expose] noncomputable def sylowInf (N : Subgroup D) [N.Normal] (S : Sylow 2 D) : Sylow 2 ↥N :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : IsSylowIn 2 ((S : Subgroup D) ⊓ N) N :=
    isSylowIn_inf_of_isSubnormal isSubnormal_top_of_normal
      ⟨le_top, S.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  (hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm).toSylow hsyl.2.2

theorem coe_sylowInf (N : Subgroup D) [N.Normal] (S : Sylow 2 D) :
    ((sylowInf N S : Sylow 2 ↥N) : Subgroup ↥N) = ((S : Subgroup D) ⊓ N).subgroupOf N :=
  rfl

theorem card_sylow_eq_mul_index (N : Subgroup D) [N.Normal] {n : ℕ} (hN : N.index = 2 ^ n)
    (S : Sylow 2 D) :
    Nat.card (S : Subgroup D) = Nat.card ↥((S : Subgroup D) ⊓ N) * 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ↥((S : Subgroup D) ⊓ N) = 2 ^ (Nat.card ↥N).factorization 2 := by
    rw [← Sylow.card_eq_multiplicity (sylowInf N S), coe_sylowInf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv.symm
  have h2 : Nat.card D = Nat.card ↥N * 2 ^ n := by rw [← hN, Subgroup.card_mul_index]
  rw [Sylow.card_eq_multiplicity, h1, h2, Nat.factorization_mul Nat.card_pos.ne'
    (by positivity), Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, pow_add]

theorem exists_sylow_quotient_of_setting (hS : F618RecogSetting D) (S : Sylow 2 D) :
    ∃ Q : Sylow 2 (TwoResidualQuot D),
      Nonempty (↥((S : Subgroup D) ⊓ twoResidual ⊤) ≃* ↥(Q : Subgroup (TwoResidualQuot D))) := by
  have := twoResidual_top_normal (D := D)
  have hodd : Odd (Nat.card (Subgroup.center ↥(twoResidual (⊤ : Subgroup D)))) := by
    obtain ⟨k, hk⟩ := hS.center.exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  obtain ⟨Q, ⟨eQ⟩⟩ := exists_sylow_quotient_mulEquiv _ hodd (sylowInf (twoResidual ⊤) S)
  exact ⟨Q, ⟨(Subgroup.subgroupOfEquivOfLe inf_le_right).symm.trans eQ⟩⟩

end SettingSylow

section Transport

open CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank

variable {D : Type} [Group D] [Finite D]

noncomputable def mulEquivTwoResidualQuot (hL : twoResidual (⊤ : Subgroup D) = ⊤)
    (hZ : Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) = ⊥) : D ≃* TwoResidualQuot D :=
  ((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)).trans
    QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)

theorem isHatAlt_of_setting (hS : F618RecogSetting D) (hL : twoResidual (⊤ : Subgroup D) = ⊤)
    (hZ : Nat.card (Subgroup.center ↥(twoResidual (⊤ : Subgroup D))) = 3) {n : ℕ}
    (e : TwoResidualQuot D ≃* ↥(alternatingGroup (Fin n))) : IsHatAlt n D := by
  let ε : D ≃* ↥(twoResidual (⊤ : Subgroup D)) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)
  have hq := CFSG.Wreathed.LocalOddCorePerfectNormalizer.quasisimple_of_equiv ε hS.quasisimple
  refine ⟨⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩, ?_, ?_⟩
  · rw [← hZ, ← Subgroup.map_center_eq ε]
    exact Nat.card_congr ((Subgroup.center D).equivMapOfInjective _ ε.injective).toEquiv
  · exact ⟨(QuotientGroup.congr _ _ ε (Subgroup.map_center_eq ε)).trans e⟩

omit [Finite D] in
theorem card_twoResidualQuot {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (eK : TwoResidualQuot D ≃* StatedProj (StatedSL 2 K)) :
    Nat.card (TwoResidualQuot D) = p ^ f * (((p ^ f) ^ 2 - 1) / 2) := by
  rw [Nat.card_congr (eK.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).toEquiv,
    CFSG.SectionRank.OddCover.card_psl_two hp hp2 hK]

theorem card_center_eq_one_or_three (hS : F618RecogSetting D)
    (h3 : Nat.card (Subgroup.center ↥(twoResidual (⊤ : Subgroup D))) ≤ 3) :
    Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) = ⊥ ∨
      Nat.card (Subgroup.center ↥(twoResidual (⊤ : Subgroup D))) = 3 := by
  obtain ⟨k, hk⟩ := hS.center.exists_card_eq
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k
  · exact Or.inl (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
  · exact Or.inr (by simpa using hk)

theorem nonempty_mulEquiv_pgl2_of_setting (hS : F618RecogSetting D)
    (hZ : Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) = ⊥)
    (hidx : (twoResidual (⊤ : Subgroup D)).index = 2) {K : Type} [Field K] [Finite K] {p : ℕ}
    [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hK : Nat.card K = p)
    (e : TwoResidualQuot D ≃* StatedProj (StatedSL 2 K)) :
    Nonempty (D ≃* GL (Fin 2) K ⧸ StatedScalars (Fin 2) K) := by
  have := twoResidual_top_normal (D := D)
  let eL : ↥(twoResidual (⊤ : Subgroup D)) ≃* PSL2 K :=
    ((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
      e).trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  let c : D →* MulAut ↥(twoResidual (⊤ : Subgroup D)) := MulAut.conjNormal
  have hinj : Function.Injective c := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (twoResidual (⊤ : Subgroup D) : Set D) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := congrArg (fun f : MulAut ↥(twoResidual (⊤ : Subgroup D)) =>
        ((f ⟨l, hl⟩ : ↥(twoResidual (⊤ : Subgroup D))) : D)) (MonoidHom.mem_ker.mp hx)
      simp only [c, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc l * x = x * l * x⁻¹ * x := by rw [h1]
        _ = x * l := by group
    have hxL : x ∈ twoResidual (⊤ : Subgroup D) := by
      have h := CFSG.centralizer_generalizedFitting_le D
      rw [hS.fitting] at h
      exact h hxC
    have hxZ : (⟨x, hxL⟩ : ↥(twoResidual (⊤ : Subgroup D))) ∈
        Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) l l.2)
    rw [hZ, Subgroup.mem_bot] at hxZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxZ
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp.out, hp.out.odd_of_ne_two (by omega), le_rfl, by rw [hK, pow_one]⟩
  have hcard : Nat.card D = Nat.card (MulAut ↥(twoResidual (⊤ : Subgroup D))) := by
    rw [← Subgroup.card_mul_index (twoResidual (⊤ : Subgroup D)), hidx,
      Nat.card_congr (MulAut.congr eL).toEquiv,
      Nat.card_congr (mulAutPSL2EquivPGL2 K hp5 hK).toEquiv,
      Nat.card_congr eL.toEquiv, psl2_card_formula K hodd, pgl2_card_formula K]
    have h2 : 2 ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
      rw [hK]
      obtain ⟨m, hm⟩ := hp.out.odd_of_ne_two (by omega)
      rw [hm]
      exact Dvd.dvd.mul_left ⟨2 * m * m + 2 * m, by rw [Nat.sub_eq_of_eq_add]; ring⟩ _
    exact Nat.div_mul_cancel h2
  have hbij : Function.Bijective c := (Nat.bijective_iff_injective_and_card c).mpr ⟨hinj, hcard⟩
  exact ⟨((MulEquiv.ofBijective c hbij).trans (MulAut.congr eL)).trans
    ((mulAutPSL2EquivPGL2 K hp5 hK).trans
      (QuotientGroup.quotientMulEquivOfEq Matrix.GeneralLinearGroup.center_eq_range_scalar))⟩

end Transport

section SettingSQT

@[expose] def NativeSQTSection : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsSQTKCat X →
    ∀ (H : Subgroup X) (N : Subgroup H) [N.Normal] [IsSimpleGroup (H ⧸ N)],
      (∃ a b : H ⧸ N, a * b ≠ b * a) → CFSG.IsStronglyQuasithin (H ⧸ N)

structure F618RecogSettingSQT (D : Type) [Group D] [Finite D] : Prop
    extends F618RecogSetting D where
  sqt : CFSG.IsStronglyQuasithin (TwoResidualQuot D)

theorem isStronglyQuasithin_of_isQuasisimple (hQ : NativeSQTSection) {D X : Type} [Group D]
    [Group X] [Finite X] (hX : CFSG.SectionRank.IsSQTKCat X) (e : D ≃* X ⧸ CFSG.pPrimeCore 3 X)
    {L : Subgroup D} (hq : CFSG.IsQuasisimple ↥L) :
    CFSG.IsStronglyQuasithin (↥L ⧸ Subgroup.center ↥L) := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  set H : Subgroup X := (L.map e.toMonoidHom).comap π with hH
  have hmemL : ∀ h : ↥H, e.symm (π h) ∈ L := by
    intro h
    obtain ⟨l, hl, hle⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp h.2)
    have : e.symm (π h) = l := by
      rw [← hle]
      exact e.symm_apply_apply l
    rw [this]
    exact hl
  let ψ : ↥H →* ↥L :=
    (e.symm.toMonoidHom.comp (π.comp H.subtype)).codRestrict L hmemL
  have hψ : Function.Surjective ψ := by
    intro l
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 X) (e l)
    have hxH : x ∈ H := by
      rw [hH, Subgroup.mem_comap, hx]
      exact Subgroup.mem_map_of_mem _ l.2
    refine ⟨⟨x, hxH⟩, Subtype.ext ?_⟩
    change e.symm (π x) = l
    rw [hx, MulEquiv.symm_apply_apply]
  let φ : ↥H →* ↥L ⧸ Subgroup.center ↥L := (QuotientGroup.mk' (Subgroup.center ↥L)).comp ψ
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hψ
  let iso : ↥H ⧸ φ.ker ≃* ↥L ⧸ Subgroup.center ↥L :=
    QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
  have : IsSimpleGroup (↥H ⧸ φ.ker) := iso.isSimpleGroup
  have hnonab : ∃ a b : ↥H ⧸ φ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    refine ⟨iso.symm a, iso.symm b, fun h => hab ?_⟩
    have := congrArg iso h
    simpa using this
  have : Finite D := Finite.of_equiv _ e.symm.toEquiv
  exact CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv iso.symm (hQ X hX H φ.ker hnonab)

theorem f618RecogSettingSQT_of (hC : NativeTheoremCSection) (hQ : NativeSQTSection) {D : Type}
    [Group D] [Finite D]
    (hX : ∃ (X : Type) (_ : Group X) (_ : Finite X), CFSG.SectionRank.IsSQTKCat X ∧
      Nonempty (D ≃* X ⧸ CFSG.pPrimeCore 3 X))
    (hF : CFSG.generalizedFitting D = twoResidual (⊤ : Subgroup D))
    (hL : CFSG.IsQuasisimple ↥(twoResidual (⊤ : Subgroup D))) : F618RecogSettingSQT D := by
  refine ⟨f618RecogSetting_of hC hX hF hL, ?_⟩
  obtain ⟨X, _, _, hsq, ⟨e⟩⟩ := hX
  exact isStronglyQuasithin_of_isQuasisimple hQ hsq e hL

end SettingSQT

end F6

end CFSG.Quasithin
