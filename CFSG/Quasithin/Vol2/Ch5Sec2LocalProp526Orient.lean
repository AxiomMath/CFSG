module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Tr
public import CFSG.Quasithin.Recognition.F112WSetup
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.CGT.Timmesfeld75.Lemma27

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_centerOf_eq (Q : Subgroup G) :
    Nat.card ↥(centerOf Q) = Nat.card ↥(Subgroup.center ↥Q) := by
  have h : (Subgroup.center ↥Q).map Q.subtype = centerOf Q := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨h, hh⟩)
    · rintro ⟨hxQ, hxC⟩
      refine ⟨⟨x, hxQ⟩, Subgroup.mem_center_iff.mpr fun h => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hxC h h.2
  rw [← h, Subgroup.card_map_of_injective Q.subtype_injective]

theorem le_centralizer_of_isL2Quot {L Z : Subgroup G} {n f : ℕ} (hn : 2 ≤ n) (hfn : f < 2 * n)
    (hL : IsL2Quot n (oTwoQuot ↥L)) (hZ : Nat.card Z = 2 ^ f)
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G))
    (hOZ : pCoreOf 2 L ≤ Subgroup.centralizer (Z : Set G)) :
    L ≤ Subgroup.centralizer (Z : Set G) := by
  classical
  obtain ⟨e⟩ := hL
  set ρ₀ : ↥L →* MulAut ↥Z :=
    (Subgroup.normalizerMonoidHom Z).comp (Subgroup.inclusion hLZ) with hρ₀
  have hρ₀v : ∀ (l : ↥L) (z : ↥Z), ((ρ₀ l z : ↥Z) : G) = l * z * (l : G)⁻¹ := fun l z =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Z _ z
  suffices hK : ρ₀.ker = ⊤ by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 : ρ₀ ⟨l, hl⟩ = 1 := by
      have : (⟨l, hl⟩ : ↥L) ∈ ρ₀.ker := by rw [hK]; exact Subgroup.mem_top _
      exact this
    have h2 := congrArg (fun φ : MulAut ↥Z => ((φ ⟨z, hz⟩ : ↥Z) : G)) h1
    simp only [hρ₀v, MulAut.one_apply] at h2
    calc z * l = (l * z * l⁻¹) * l := by rw [h2]
      _ = l * z := by group
  have hOK : Open.pCore 2 ↥L ≤ ρ₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun z => Subtype.ext ?_
    rw [hρ₀v, MulAut.one_apply]
    have hxO : (x : G) ∈ pCoreOf 2 L := ⟨x, hx, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp (hOZ hxO) z z.2
    calc (x : G) * z * (x : G)⁻¹ = z * x * (x : G)⁻¹ := by rw [h]
      _ = z := by group
  set π : ↥L →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Open.pCore 2 ↥L)) with hπ
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = Open.pCore 2 ↥L := by
    ext x
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have : (ρ₀.ker.map π).Normal := (MonoidHom.normal_ker ρ₀).map π hπs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ₀.ker.map π) with hb | ht
  ·
    exfalso
    have hKO : ρ₀.ker ≤ π.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      have : π x ∈ ρ₀.ker.map π := ⟨x, hx, rfl⟩
      rw [hb] at this
      exact this
    let θ : ↥L ⧸ ρ₀.ker →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
      QuotientGroup.lift ρ₀.ker π hKO
    have hθ : Function.Surjective θ := by
      intro y
      obtain ⟨x, rfl⟩ := hπs y
      exact ⟨QuotientGroup.mk x, rfl⟩
    have hρ := QuotientGroup.kerLift_injective ρ₀
    have hdvd := Subgroup.card_dvd_of_surjective hθ
    rw [card_psl_two_gf2 n (by omega)] at hdvd
    by_cases hn3 : n = 3
    · subst hn3
      have := CGT.Timmesfeld75.lemma27_psl2_eight θ hθ (QuotientGroup.kerLift ρ₀) hρ hZ
      omega
    · have h4n : (2 ^ n) ^ 2 = 4 ^ n := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      have := CGT.Timmesfeld75.lemma27_psl2 hn hn3 (by rw [h4n]; exact hdvd)
        (QuotientGroup.kerLift ρ₀) hρ hZ
      omega
  ·
    rw [eq_top_iff]
    intro x _
    have : π x ∈ ρ₀.ker.map π := by rw [ht]; exact Subgroup.mem_top _
    obtain ⟨k, hk, hkx⟩ := this
    have hxk : k⁻¹ * x ∈ Open.pCore 2 ↥L := by
      rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
    have := ρ₀.ker.mul_mem hk (hOK hxk)
    simpa using this

theorem centerOf_le_centralizer_of_hyp111 {L1 L2 S Q : Subgroup G} (hR : Hyp111R L1 L2 S)
    (hQS : Q ≤ S) (hOQ : pCoreOf 2 L1 ≤ Q) (hLQ : L1 ≤ Subgroup.normalizer (Q : Set G))
    (hZL : L1 ≤ Subgroup.centralizer (centerOf Q : Set G)) :
    centerOf S ≤ Subgroup.centralizer (L1 : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro z hz
  obtain ⟨hzS, hzC⟩ := Subgroup.mem_inf.mp hz
  have hSP := F112W.isSylowTwoOf_parabolic hR
  have hOP : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := F7.isSylowTwoOf_pCoreOf_le hSP
  have hzP : z ∈ L1 ⊔ bigB L1 L2 S := hSP.1 hzS
  have hzO : z ∈ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := by
    apply F1.parabolic_charTwo hR
    refine Subgroup.mem_inf.mpr ⟨hzP, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp hzC y (hOP hy)
  have hPL : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) := F1.parabolic_le_normalizer hR
  have hL1P : L1 ≤ L1 ⊔ bigB L1 L2 S := le_sup_left
  have hc : ∀ l ∈ L1, z * l * z⁻¹ * l⁻¹ ∈ centerOf Q := by
    intro l hl
    have hcO : z * l * z⁻¹ * l⁻¹ ∈ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := by
      have h1 : l * z⁻¹ * l⁻¹ ∈ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (hL1P hl)) z⁻¹).mp
          (inv_mem hzO)
      have := (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)).mul_mem hzO h1
      simpa [mul_assoc] using this
    have hcL : z * l * z⁻¹ * l⁻¹ ∈ L1 := by
      have h1 : z * l * z⁻¹ ∈ L1 := (Subgroup.mem_normalizer_iff.mp (hPL hzP) l).mp hl
      exact L1.mul_mem h1 (L1.inv_mem hl)
    have hcQ : z * l * z⁻¹ * l⁻¹ ∈ Q := by
      apply hOQ
      rw [← F1.inf_pCoreOf_parabolic_eq hR]
      exact Subgroup.mem_inf.mpr ⟨hcO, hcL⟩
    refine Subgroup.mem_inf.mpr ⟨hcQ, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    obtain ⟨y, hyQ, rfl⟩ : ∃ y ∈ Q, x = l * y * l⁻¹ := by
      refine ⟨l⁻¹ * x * l, ?_, by group⟩
      have := (Subgroup.mem_normalizer_iff.mp (hLQ (L1.inv_mem hl)) x).mp hx
      simpa using this
    have hxz := Subgroup.mem_centralizer_iff.mp hzC _ (hQS hx)
    have hyz := Subgroup.mem_centralizer_iff.mp hzC y (hQS hyQ)
    have hyz' : y * z⁻¹ = z⁻¹ * y := by
      calc y * z⁻¹ = z⁻¹ * (z * y) * z⁻¹ := by group
        _ = z⁻¹ * (y * z) * z⁻¹ := by rw [hyz]
        _ = z⁻¹ * y := by group
    calc l * y * l⁻¹ * (z * l * z⁻¹ * l⁻¹) = (l * y * l⁻¹ * z) * l * z⁻¹ * l⁻¹ := by group
      _ = (z * (l * y * l⁻¹)) * l * z⁻¹ * l⁻¹ := by rw [hxz]
      _ = z * l * (y * z⁻¹) * l⁻¹ := by group
      _ = z * l * (z⁻¹ * y) * l⁻¹ := by rw [hyz']
      _ = z * l * z⁻¹ * l⁻¹ * (l * y * l⁻¹) := by group
  let φ : ↥L1 →* ↥(centerOf Q) :=
    { toFun := fun l => ⟨z * l * z⁻¹ * (l : G)⁻¹, hc l l.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, MulMemClass.mk_mul_mk]
        have hcomm : (z * b * z⁻¹ * (b : G)⁻¹) * a = a * (z * b * z⁻¹ * (b : G)⁻¹) :=
          Subgroup.mem_centralizer_iff.mp (hZL a.2) _ (hc b b.2)
        calc z * (a * b) * z⁻¹ * ((a : G) * b)⁻¹ =
            z * a * z⁻¹ * ((a : G)⁻¹ * (a * (z * b * z⁻¹ * (b : G)⁻¹))) * (a : G)⁻¹ := by
              group
          _ = z * a * z⁻¹ * ((a : G)⁻¹ * ((z * b * z⁻¹ * (b : G)⁻¹) * a)) * (a : G)⁻¹ := by
              rw [hcomm]
          _ = z * a * z⁻¹ * (a : G)⁻¹ * (z * b * z⁻¹ * (b : G)⁻¹) := by group }
  have hφ : ∀ l : ↥L1, ((φ l : ↥(centerOf Q)) : G) = z * l * z⁻¹ * (l : G)⁻¹ := fun _ => rfl
  have hker : (S ⊓ L1).subgroupOf L1 ≤ φ.ker := by
    intro s hs
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hφ]
    have h := Subgroup.mem_centralizer_iff.mp hzC s (Subgroup.mem_subgroupOf.mp hs).1
    show z * s * z⁻¹ * (s : G)⁻¹ = 1
    rw [← h]
    group
  have hodd : ¬ 2 ∣ φ.ker.index := fun h2 =>
    hR.hyp.h1.sylow.2.2 (h2.trans (Subgroup.index_dvd_of_le hker))
  have hZ2 : IsPGroup 2 ↥(centerOf Q) :=
    hR.hyp.h1.pgroup.to_le (inf_le_left.trans hQS)
  have hrange : Nat.card ↥φ.range = 1 := by
    rcases (hZ2.to_subgroup φ.range).card_eq_or_dvd with h | h
    · exact h
    · exfalso
      rw [← Subgroup.index_ker] at h
      exact hodd h
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl1 : φ ⟨l, hl⟩ = 1 := by
    have hmem : φ ⟨l, hl⟩ ∈ φ.range := ⟨⟨l, hl⟩, rfl⟩
    rw [Subgroup.card_eq_one.mp hrange] at hmem
    exact hmem
  have h := congrArg Subtype.val hl1
  rw [hφ] at h
  simp only [OneMemClass.coe_one] at h
  calc l * z = (z * l * z⁻¹ * l⁻¹)⁻¹ * (z * l) := by group
    _ = z * l := by rw [h, inv_one, one_mul]

theorem stmt5_2_6_orient_holds : Stmt5_2_6_orient := by
  intro G _ _ L1 L2 S h111 _ _ _ _ he
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts h111
  have hO1S : pCoreOf 2 L1 ≤ S := (F7.isSylowTwoOf_pCoreOf_le h111.h1.sylow).trans inf_le_left
  have hO1N : L1 ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) := le_normalizer_pCoreOf 2 L1
  have hcent : ∀ {Q : Subgroup G} {n f : ℕ}, 2 ≤ n → f < 2 * n → IsL2Quot n (oTwoQuot ↥L1) →
      Nat.card ↥(Subgroup.center ↥Q) = 2 ^ f → pCoreOf 2 L1 ≤ Q →
      L1 ≤ Subgroup.normalizer (Q : Set G) →
      L1 ≤ Subgroup.centralizer (centerOf Q : Set G) := by
    intro Q n f hn hfn hq hZ hOQ hLQ
    refine le_centralizer_of_isL2Quot hn hfn hq (by rw [card_centerOf_eq, hZ])
      (hLQ.trans (A4.normalizer_le_normalizer_centerOf Q)) fun o ho => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 o (hOQ ho)).symm
  rcases he with h3 | h4 | h6
  ·
    obtain ⟨f, hf, -, hq1, -, hsp, -⟩ := h3
    have hSy : IsSylowTwoOf S (L1 ⊔ S) :=
      F7.isSylowTwoOf_mono_right (F112W.isSylowTwoOf_parabolic hR) le_sup_right
        (sup_le_sup_left le_sup_right L1)
    have hOQ : pCoreOf 2 L1 ≤ pCoreOf 2 (L1 ⊔ S) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L1).trans le_sup_left)
        (sup_le hO1N (h111.h1.normalizes.trans (normalizer_le_normalizer_pCoreOf 2 L1)))
        (pCoreOf_isPGroup 2 L1)
    have hLQ : L1 ≤ Subgroup.normalizer (pCoreOf 2 (L1 ⊔ S) : Set G) :=
      le_sup_left.trans (le_normalizer_pCoreOf 2 _)
    exact centerOf_le_centralizer_of_hyp111 hR (F7.isSylowTwoOf_pCoreOf_le hSy) hOQ hLQ
      (hcent hf (by omega) hq1 hsp.2.2 hOQ hLQ)
  ·
    obtain ⟨f, hf, -, hq1, hsp, -, -⟩ := h4
    exact centerOf_le_centralizer_of_hyp111 hR hO1S le_rfl hO1N
      (hcent (n := 3 * f) (by omega) (by omega) hq1 hsp.2.2 le_rfl hO1N)
  ·
    obtain ⟨f, hf, -, hq1, hsp, -, -, -⟩ := h6
    exact centerOf_le_centralizer_of_hyp111 hR hO1S le_rfl hO1N
      (hcent hf (by omega) hq1 hsp.2.2 le_rfl hO1N)

end CFSG.Quasithin.H13
