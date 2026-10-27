module

public import CFSG.RankThree.GF2n.Tim79a34ResidualMaxAb

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Quasithin CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open scoped commutatorElement Matrix

section Helpers

variable {G : Type} [Group G]

theorem residual_le_normalizer_of_conj_mem {S R : Subgroup G}
    (h : ∀ m ∈ S, ∀ r ∈ R, m * r * m⁻¹ ∈ R) : S ≤ Subgroup.normalizer (R : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact h m hm x
  · intro hx
    have h' := h m⁻¹ (S.inv_mem hm) _ hx
    rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x by group] at h'

theorem residual_normalizer_le_of_isTI [Finite G] {V M Y : Subgroup G} (hTI : IsTI V)
    (hN : Subgroup.normalizer (V : Set G) = M) (hY : Y ≤ V) (hne : Y ≠ ⊥) :
    Subgroup.normalizer (Y : Set G) ≤ M := by
  intro g hg
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  rw [← hN, ← conjSubgroup_eq_self_iff]
  refine conjSubgroup_eq_of_isTI hTI fun h => hy1 ?_
  have h1 : g * (y : G) * g⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hg y).mp y.2
  have h2 : g * (y : G) * g⁻¹ ∈ V ⊓ conjSubgroup g V := by
    refine Subgroup.mem_inf.mpr ⟨hY h1, mem_conjSubgroup.mpr ?_⟩
    rw [show g⁻¹ * (g * (y : G) * g⁻¹) * g = y by group]
    exact hY y.2
  rw [h, Subgroup.mem_bot] at h2
  apply Subtype.ext
  simpa using h2

theorem residual_exists_mul_of_mem_sup {P R : Subgroup G}
    (h : P ≤ Subgroup.normalizer (R : Set G)) {y : G} (hy : y ∈ P ⊔ R) :
    ∃ p ∈ P, ∃ r ∈ R, y = p * r := by
  rw [Subgroup.sup_eq_closure] at hy
  refine Subgroup.closure_induction (p := fun x _ => ∃ p ∈ P, ∃ r ∈ R, x = p * r)
    ?_ ?_ ?_ ?_ hy
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, R.one_mem, (mul_one x).symm⟩
    · exact ⟨1, P.one_mem, x, hx, (one_mul x).symm⟩
  · exact ⟨1, P.one_mem, 1, R.one_mem, (mul_one 1).symm⟩
  · rintro x y _ _ ⟨p₁, hp₁, r₁, hr₁, rfl⟩ ⟨p₂, hp₂, r₂, hr₂, rfl⟩
    refine ⟨p₁ * p₂, P.mul_mem hp₁ hp₂, (p₂⁻¹ * r₁ * p₂) * r₂, ?_, by group⟩
    refine R.mul_mem ?_ hr₂
    have := (Subgroup.mem_normalizer_iff.mp (h (P.inv_mem hp₂)) r₁).mp hr₁
    simpa using this
  · rintro x _ ⟨p, hp, r, hr, rfl⟩
    refine ⟨p⁻¹, P.inv_mem hp, p * r⁻¹ * p⁻¹, ?_, by group⟩
    exact (Subgroup.mem_normalizer_iff.mp (h hp) r⁻¹).mp (R.inv_mem hr)

end Helpers

section Local

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G} {n : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 1}
  {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}

theorem normalizer_P_eq_M (hc : MinCex M V Q P H) : Subgroup.normalizer (P : Set G) = M := by
  have hPne : P ≠ ⊥ := by
    intro h
    exact hc.V_ne_bot (le_bot_iff.mp (h ▸ hc.V_le_P))
  by_contra hne
  exact hc.maxLocal.2 _ (lt_of_le_of_ne hc.M_le_normalizer_P (Ne.symm hne))
    ⟨P, hPne, hc.isPGroup_P, rfl⟩

theorem le_P_of_normalized_two_subgroup (hc : MinCex M V Q P H)
    (hQP : Q ⊓ pResidual 2 G = P) (hPG : P ≤ pResidual 2 G)
    {R : Subgroup G} (hRG : R ≤ pResidual 2 G) (hR2 : IsPGroup 2 R)
    (hMR : ∀ m ∈ M ⊓ pResidual 2 G, ∀ r ∈ R, m * r * m⁻¹ ∈ R) : R ≤ P := by
  haveI : (pResidual 2 G).Normal := G6.pResidual_normal_aux 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQM : Q ≤ M := by
    rw [hc.hQ]
    exact (inSubgroup_pCore_two M).2.1
  have hPQM : P ≤ M := hc.P_le_Q.trans hQM
  have hPM : P ≤ M ⊓ pResidual 2 G := le_inf hPQM hPG
  have hNP := normalizer_P_eq_M hc
  have hRM : R ⊓ M ≤ P := by
    have h := le_pCore_of_normal_inf (M := M) (G₀ := pResidual 2 G) (R := R ⊓ M)
      (fun x hx => ⟨hx.2, hRG hx.1⟩)
      (fun m hm r hr => ⟨hMR m hm r hr.1,
        M.mul_mem (M.mul_mem (Subgroup.mem_inf.mp hm).1 hr.2)
          (M.inv_mem (Subgroup.mem_inf.mp hm).1)⟩)
      (hR2.to_le inf_le_left)
    rw [← hc.hQ] at h
    rw [← hQP]
    exact le_inf h (inf_le_left.trans hRG)
  by_contra hRP
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    hPM.trans (residual_le_normalizer_of_conj_mem hMR)
  have hD2 : IsPGroup 2 ↥(P ⊔ R) := hc.isPGroup_P.to_sup_of_normal_right' hR2 hPR
  have hPD : P ≤ P ⊔ R := le_sup_left
  haveI : Group.IsNilpotent ↥(P ⊔ R) := hD2.isNilpotent
  have hnc : NormalizerCondition ↥(P ⊔ R) := Group.normalizerCondition_of_isNilpotent
  have hne : ¬ (P ⊔ R) ≤ P := fun h => hRP (le_sup_right.trans h)
  have hlt : P.subgroupOf (P ⊔ R) < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hne (Subgroup.subgroupOf_eq_top.mp h)
  have hlt' := hnc _ hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hPD] at hlt'
  obtain ⟨y, hy1, hy2⟩ := SetLike.exists_of_lt hlt'
  rw [Subgroup.mem_subgroupOf] at hy1 hy2
  have hyM : (y : G) ∈ M := hNP ▸ hy1
  obtain ⟨p, hp, r, hr, hyr⟩ := residual_exists_mul_of_mem_sup hPR y.2
  have hrM : r ∈ M := by
    have : r = p⁻¹ * (y : G) := by rw [hyr]; group
    rw [this]
    exact M.mul_mem (M.inv_mem (hPQM hp)) hyM
  have hrP : r ∈ P := hRM ⟨hr, hrM⟩
  exact hy2 (by rw [hyr]; exact P.mul_mem hp hrP)

theorem normalizer_inf_residual_le (cfg : ResCfg M V Q P H Φ ψ a T)
    (hX : xOf V H ≤ pResidual 2 G) (hQP : Q ⊓ pResidual 2 G = P) (hPG : P ≤ pResidual 2 G)
    {R : Subgroup G} (hRG : R ≤ pResidual 2 G) (hRne : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hMR : ∀ m ∈ M ⊓ pResidual 2 G, ∀ r ∈ R, m * r * m⁻¹ ∈ R) :
    Subgroup.normalizer (R : Set G) ⊓ pResidual 2 G ≤ M := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  haveI : (pResidual 2 G).Normal := G6.pResidual_normal_aux 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQM : Q ≤ M := by
    rw [hc.hQ]
    exact (inSubgroup_pCore_two M).2.1
  have hPM : P ≤ M ⊓ pResidual 2 G := le_inf (hc.P_le_Q.trans hQM) hPG
  have hRP : R ≤ P := le_P_of_normalized_two_subgroup hc hQP hPG hRG hR2 hMR
  have hMN : M ⊓ pResidual 2 G ≤ Subgroup.normalizer (R : Set G) :=
    residual_le_normalizer_of_conj_mem hMR
  set Z : Subgroup G := R ⊓ Subgroup.centralizer (R : Set G) with hZdef
  have hZR : Z ≤ R := inf_le_left
  have hZP : Z ≤ P := hZR.trans hRP
  have hZne : Z ≠ ⊥ := by
    haveI : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hRne
    haveI : Nontrivial ↥(Subgroup.center ↥R) := (hR2.center_nontrivial)
    obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥R))
    have hzZ : ((z : ↥R) : G) ∈ Z := by
      refine ⟨(z : ↥R).2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      have := Subgroup.mem_center_iff.mp z.2 ⟨h, hh⟩
      exact congrArg Subtype.val this
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨_, hzZ⟩, fun h => hz1 ?_⟩
    have h' : ((z : ↥R) : G) = 1 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hZab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp hx.2 y hy.1).symm
  have hZV : ∀ z ∈ Z, ∀ v ∈ V, z * v = v * z := fun z hz v hv => by
    have hzP : z ∈ Q ⊓ Subgroup.centralizer (V : Set G) := hc.hP ▸ hZP hz
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzP).2 v hv).symm
  have hZn : ∀ m ∈ Subgroup.normalizer (R : Set G), ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := by
    intro m hm z hz
    have h1 : m * z * m⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hm z).mp hz.1
    refine ⟨h1, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    have hr' : m⁻¹ * r * m ∈ R := by
      have h2 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (R : Set G)).inv_mem hm)
        r).mp hr
      simpa using h2
    have hc' := Subgroup.mem_centralizer_iff.mp hz.2 _ hr'
    calc r * (m * z * m⁻¹) = m * ((m⁻¹ * r * m) * z) * m⁻¹ := by group
      _ = m * (z * (m⁻¹ * r * m)) * m⁻¹ := by rw [hc']
      _ = (m * z * m⁻¹) * r := by group
  have hUab : ∀ x ∈ Z ⊔ V, ∀ y ∈ Z ⊔ V, x * y = y * x := by
    intro x hx y hy
    obtain ⟨z₁, hz₁, v₁, hv₁, rfl⟩ := exists_mul_of_mem_sup hZV hx
    obtain ⟨z₂, hz₂, v₂, hv₂, rfl⟩ := exists_mul_of_mem_sup hZV hy
    have e1 : v₁ * z₂ = z₂ * v₁ := (hZV z₂ hz₂ v₁ hv₁).symm
    have e2 : v₂ * z₁ = z₁ * v₂ := (hZV z₁ hz₁ v₂ hv₂).symm
    have e3 : z₁ * z₂ = z₂ * z₁ := hZab _ hz₁ _ hz₂
    have e4 : v₁ * v₂ = v₂ * v₁ :=
      congrArg Subtype.val (hc.elemAb.1.is_comm.comm ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩)
    calc z₁ * v₁ * (z₂ * v₂) = z₁ * (v₁ * z₂) * v₂ := by group
      _ = z₁ * (z₂ * v₁) * v₂ := by rw [e1]
      _ = (z₁ * z₂) * (v₁ * v₂) := by group
      _ = (z₂ * z₁) * (v₂ * v₁) := by rw [e3, e4]
      _ = z₂ * (z₁ * v₂) * v₁ := by group
      _ = z₂ * (v₂ * z₁) * v₁ := by rw [e2]
      _ = z₂ * v₂ * (z₁ * v₁) := by group
  have hVn : ∀ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ V := fun m hm v hv => by
    have hmN : m ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq]
      exact hm
    exact (Subgroup.mem_normalizer_iff.mp hmN v).mp hv
  have hUn : ∀ m ∈ M ⊓ pResidual 2 G, ∀ x ∈ Z ⊔ V, m * x * m⁻¹ ∈ Z ⊔ V := by
    intro m hm x hx
    obtain ⟨z, hz, v, hv, rfl⟩ := exists_mul_of_mem_sup hZV hx
    have e : m * (z * v) * m⁻¹ = (m * z * m⁻¹) * (m * v * m⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem_sup (hZn m (hMN hm) z hz) (hVn m (Subgroup.mem_inf.mp hm).1 v hv)
  have hUM : Z ⊔ V ≤ M ⊓ pResidual 2 G :=
    sup_le (hZP.trans hPM) (hc.V_le_P.trans hPM)
  have hZV' : Z ⊔ V ≤ V :=
    le_V_of_abelian_normalized cfg hX hQP hPG hUM le_sup_right hUab hUn
  have hZle : Z ≤ V := le_sup_left.trans hZV'
  have hZnorm : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Z : Set G) :=
    residual_le_normalizer_of_conj_mem hZn
  intro l hl
  exact residual_normalizer_le_of_isTI hc.ti hc.normalizer_eq hZle hZne (hZnorm hl.1)

end Local

theorem residualMaxLocalStatement_holds :
    ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), TwoEndHyp M V Q P H →
      Subgroup.center (Xbar V H) = ⊥ →
      (∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H)) →
      P.relIndex Q = 2 →
      (∃ (N : Subgroup G) (_ : N.Normal), IsPGroup 2 (G ⧸ N) ∧ ¬ Q ≤ N) →
      IsMaximalTwoLocal (M.subgroupOf (pResidual 2 G)) := by
  intro G _ _ M V Q P H hH hZ hn hrel hOut
  obtain ⟨n, Φ, ψ, a, T, hn3, cfg⟩ := exists_resCfg hH hZ hn
  haveI : (pResidual 2 G).Normal := G6.pResidual_normal_aux 2
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hQP : Q ⊓ pResidual 2 G = P := inf_pResidual_eq_P hH hZ hn hrel hOut
  have hPG : P ≤ pResidual 2 G := P_le_pResidual hH hZ hn
  have hV : V ≤ pResidual 2 G := hc.V_le_P.trans hPG
  have hX : xOf V H ≤ pResidual 2 G := by
    obtain ⟨n', hn'3, ⟨e⟩⟩ := hn
    exact xOf_le_pResidual hH hn'3 e
  have hNP := normalizer_P_eq_M hc
  refine ⟨?_, fun L hML hL => ?_⟩
  · refine ⟨P.subgroupOf (pResidual 2 G), ?_, ?_, ?_⟩
    · intro h
      apply hc.V_ne_bot
      rw [eq_bot_iff]
      intro v hv
      have h1 : (⟨v, hV hv⟩ : ↥(pResidual 2 G)) ∈ P.subgroupOf (pResidual 2 G) :=
        Subgroup.mem_subgroupOf.mpr (hc.V_le_P hv)
      rw [h, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
    · exact hc.isPGroup_P.of_equiv (Subgroup.subgroupOfEquivOfLe hPG).symm
    · ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff]
      constructor
      · intro hx y
        have hxN : (x : G) ∈ Subgroup.normalizer (P : Set G) := hNP ▸ hx
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        simpa using Subgroup.mem_normalizer_iff.mp hxN (y : G)
      · intro hx
        have hxN : (x : G) ∈ Subgroup.normalizer (P : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro g
          constructor
          · intro hg
            have h1 := (hx ⟨g, hPG hg⟩).mp (Subgroup.mem_subgroupOf.mpr hg)
            simpa using Subgroup.mem_subgroupOf.mp h1
          · intro hg
            have hgG : g ∈ pResidual 2 G := by
              have := (inferInstance : (pResidual 2 G).Normal).conj_mem _ (hPG hg) (x : G)⁻¹
              simpa [mul_assoc] using this
            have h1 := (hx ⟨g, hgG⟩).mpr (by
              rw [Subgroup.mem_subgroupOf]
              simpa using hg)
            simpa using Subgroup.mem_subgroupOf.mp h1
        rw [← hNP]
        exact hxN
  · obtain ⟨R, hRne, hR2, hLR⟩ := hL
    have hRG : R.map (pResidual 2 G).subtype ≤ pResidual 2 G := Subgroup.map_subtype_le R
    have hR'ne : R.map (pResidual 2 G).subtype ≠ ⊥ := fun h =>
      hRne ((Subgroup.map_eq_bot_iff_of_injective R (pResidual 2 G).subtype_injective).mp h)
    have hR'2 : IsPGroup 2 (R.map (pResidual 2 G).subtype) := hR2.map _
    have hLmem : ∀ l ∈ L, ∀ r ∈ R, l * r * l⁻¹ ∈ R := fun l hl r hr =>
      (Subgroup.mem_normalizer_iff.mp (hLR ▸ hl) r).mp hr
    have hMR : ∀ m ∈ M ⊓ pResidual 2 G, ∀ r ∈ R.map (pResidual 2 G).subtype,
        m * r * m⁻¹ ∈ R.map (pResidual 2 G).subtype := by
      intro m hm
      rintro _ ⟨r, hr, rfl⟩
      have hm' : (⟨m, (Subgroup.mem_inf.mp hm).2⟩ : ↥(pResidual 2 G)) ∈ L :=
        hML.le (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hm).1)
      exact ⟨_, hLmem _ hm' r hr, rfl⟩
    have hLn : L.map (pResidual 2 G).subtype ≤
        Subgroup.normalizer (R.map (pResidual 2 G).subtype : Set G) := by
      refine residual_le_normalizer_of_conj_mem ?_
      rintro _ ⟨l, hl, rfl⟩ _ ⟨r, hr, rfl⟩
      exact ⟨_, hLmem l hl r hr, rfl⟩
    have hLM : L ≤ M.subgroupOf (pResidual 2 G) := fun l hl =>
      Subgroup.mem_subgroupOf.mpr (normalizer_inf_residual_le cfg hX hQP hPG hRG hR'ne hR'2 hMR
        ⟨hLn ⟨l, hl, rfl⟩, l.2⟩)
    exact absurd hLM (not_le_of_gt hML)

end CFSG.RankThree.GF2n.Tim79a
