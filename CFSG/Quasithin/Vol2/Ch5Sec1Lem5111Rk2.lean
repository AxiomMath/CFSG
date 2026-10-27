module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5111Cent
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2Lie

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def FactRank2CartanGraph : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (k : ℕ), 2 ≤ k → (IsSL3Ch5 k Y ∨ LieModel Y .PSp 2 2 k) →
    ∀ U : Subgroup Y, IsSylowTwoOf U ⊤ → ∀ α : MulAut Y, (∃ e : ℕ, α ^ 2 ^ e = 1) →
      U.map α.toMonoidHom = U →
      (∀ x ∈ Subgroup.normalizer (U : Set Y), α x * x⁻¹ ∈ U) →
      (∃ y : Y, α = MulAut.conj y) ∨
        (LieModel Y .PSL 3 2 2 ∧ (∃ y : Y, α ^ 2 = MulAut.conj y) ∧
          ∀ P : Subgroup Y, Subgroup.normalizer (U : Set Y) ≤ P → P ⋖ ⊤ →
            P.map α.toMonoidHom ≠ P)

section Alpha

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

omit [Finite G] in
noncomputable def conjAutK (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut ↥K where
  toFun n :=
    { toFun := fun x => ⟨(n : G) * x * (n : G)⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 x).mp x.2⟩
      invFun := fun x => ⟨(n : G)⁻¹ * x * (n : G), by
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ n.2) x).mp x.2
        simpa only [inv_inv] using h⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext x
    simp
  map_mul' n m := by
    ext x
    simp [mul_assoc]

noncomputable def descendAutO2 (X : Type) [Group X] : MulAut X →* MulAut (X ⧸ CFSG.pCore 2 X) where
  toFun ψ := QuotientGroup.congr _ _ ψ (CFSG.pCore_map_iso 2 ψ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' ψ φ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

omit [Finite G] in
noncomputable def alphaHom (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (O2Q K) :=
  (descendAutO2 ↥K).comp (conjAutK K)

omit [Finite G] in
theorem alphaHom_mk (s : ↥(Subgroup.normalizer (K : Set G))) (x : ↥K) :
    alphaHom K s (QuotientGroup.mk x) = QuotientGroup.mk
      ⟨(s : G) * x * (s : G)⁻¹, (Subgroup.mem_normalizer_iff.mp s.2 x).mp x.2⟩ := by
  simp only [alphaHom, MonoidHom.comp_apply]
  rfl

omit [Finite G] in
theorem alphaHom_pow_eq_one (s : ↥(Subgroup.normalizer (K : Set G))) {e : ℕ}
    (he : (s : G) ^ 2 ^ e = 1) : alphaHom K s ^ 2 ^ e = 1 := by
  have hs : s ^ 2 ^ e = 1 := Subtype.ext (by simpa using he)
  rw [← map_pow, hs, map_one]

theorem map_alphaOf_modO2Image (s : ↥(Subgroup.normalizer (K : Set G))) {A : Subgroup G}
    (hsA : (s : G) ∈ Subgroup.normalizer (A : Set G)) :
    (modO2Image K A).map (alphaHom K s).toMonoidHom = modO2Image K A := by
  refine Subgroup.eq_of_le_of_card_ge ?_
    (Subgroup.card_map_of_injective (alphaHom K s).injective).ge
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  refine ⟨⟨(s : G) * a * (s : G)⁻¹, (Subgroup.mem_normalizer_iff.mp s.2 a).mp a.2⟩, ?_, rfl⟩
  show (s : G) * a * (s : G)⁻¹ ∈ A
  exact (Subgroup.mem_normalizer_iff.mp hsA _).mp (Subgroup.mem_subgroupOf.mp ha)

omit [Finite G] in
theorem forall_comm_of_alphaHom_eq_conj (s : ↥(Subgroup.normalizer (K : Set G))) (y : ↥K)
    (h : alphaHom K s = MulAut.conj (QuotientGroup.mk y : O2Q K)) :
    ∀ k ∈ K, ((y : G)⁻¹ * s) * k * ((y : G)⁻¹ * s)⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  intro k hk
  have h1 := congrArg (fun φ : MulAut (O2Q K) => φ (QuotientGroup.mk ⟨k⁻¹, K.inv_mem hk⟩)) h
  simp only [alphaHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    at h1
  rw [QuotientGroup.eq] at h1
  have h2 := (inferInstance : (CFSG.pCore 2 ↥K).Normal).conj_mem _ h1 y⁻¹
  rw [Vol2.Ch11.SecS.pCoreOf_two_eq_map]
  refine ⟨_, h2, ?_⟩
  simp [mul_assoc]

theorem mem_normalizer_of_forall_comm {Q : Subgroup G} (hOQ : pCoreOf 2 K ≤ Q) (hQK : Q ≤ K)
    {c : G} (hc : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 K) :
    c ∈ Subgroup.normalizer (Q : Set G) := by
  refine mem_normalizer_of_conj_mem' fun q hq => ?_
  have h := Q.mul_mem (hOQ (hc q (hQK hq))) hq
  simpa [mul_assoc] using h

end Alpha

theorem map_mulAut_mul {Y : Type} [Group Y] (x y : MulAut Y) (P : Subgroup Y) :
    P.map (x * y).toMonoidHom = (P.map y.toMonoidHom).map x.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem map_mulAut_inv_map {Y : Type} [Group Y] (x : MulAut Y) (P : Subgroup Y) :
    (P.map x.toMonoidHom).map x⁻¹.toMonoidHom = P := by
  rw [← map_mulAut_mul, inv_mul_cancel]
  exact Subgroup.map_id P

theorem map_normalizer_of_map_eq {Y : Type} [Group Y] {U : Subgroup Y} {α : MulAut Y}
    (h : U.map α.toMonoidHom = U) :
    (Subgroup.normalizer (U : Set Y)).map α.toMonoidHom = Subgroup.normalizer (U : Set Y) := by
  rw [Subgroup.map_equiv_normalizer_eq, h]

theorem covBy_map_of_map_eq {Y : Type} [Group Y] {U P : Subgroup Y} {α : MulAut Y}
    (h : U.map α.toMonoidHom = U) (hNP : Subgroup.normalizer (U : Set Y) ≤ P) (hP : P ⋖ ⊤) :
    Subgroup.normalizer (U : Set Y) ≤ P.map α.toMonoidHom ∧ P.map α.toMonoidHom ⋖ ⊤ := by
  refine ⟨(map_normalizer_of_map_eq h).ge.trans (Subgroup.map_mono hNP), ?_⟩
  have key := (apply_covBy_apply_iff (MulEquiv.mapSubgroup α) (a := P) (b := ⊤)).mpr hP
  have htop : (⊤ : Subgroup Y).map α.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective α.toMonoidHom α.surjective
  rw [← htop]
  exact key

theorem three_rank2 (hF : FactL2LieParabolic) (hG : FactRank2CartanGraph)
    {G : Type} [Group G] [Finite G] {T M L H : Subgroup G} {n k : ℕ}
    (hyp : Hyp5_1_8 G T M L H n) (hBorel : E2.IsBorelIn (oTwoUpper H) (M ⊓ oTwoUpper H))
    (hk : 2 ≤ k)
    (htype : IsSL3Ch5 k (O2Q (oTwoUpper H)) ∨ LieModel (O2Q (oTwoUpper H)) .PSp 2 2 k) :
    (∀ P : Subgroup G, IsRankOneParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P →
        pCoreOf 2 (M ⊓ H) ≤ Subgroup.normalizer (P : Set G)) ∨
      (LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 ∧
        (oTwoUpper H ⊔ pCoreOf 2 H).relIndex (oTwoUpper H ⊔ pCoreOf 2 (M ⊓ H)) = 2 ∧
        E2.IsDiagramNontrivial (pCoreOf 2 (M ⊓ H)) (oTwoUpper H) (T ⊓ oTwoUpper H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hMK := hyp.borel_eq hBorel
  have hSK := hyp.inf_oTwoUpper_eq hBorel
  have hOMK := hyp.pCoreOf_inf_oTwoUpper_eq hBorel
  set K := oTwoUpper H with hKdef
  set S := pCoreOf 2 (M ⊓ H) with hSdef
  set Bk := K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) with hBk
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hKH : K ≤ H := oTwoUpper_le H
  have hKN : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hTK : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTH hKH hKN
  have hOS : pCoreOf 2 K ≤ T ⊓ K := F7.isSylowTwoOf_pCoreOf_le hTK
  have hOB : pCoreOf 2 K ≤ Bk := hOS.trans (le_inf hTK.1 Subgroup.le_normalizer)
  have hSMH : S ≤ M ⊓ H := pCoreOf_le 2 _
  have hSH : S ≤ H := hSMH.trans inf_le_right
  have hSN : S ≤ Subgroup.normalizer (K : Set G) := hSH.trans hKN
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 _
  have hTHK : T ⊔ K = H := by
    rw [hKdef, ← F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq hTH
  have hSTK : S ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    rw [← hOMK]
    refine le_trans (fun s hs => ?_) (normalizer_le_normalizer_pCoreOf 2 (M ⊓ K))
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hSMH hs).1, hSN hs⟩
  have hcomm : ∀ x ∈ Bk, ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ T ⊓ K := by
    intro x hx s hs
    have hxMK : x ∈ M ⊓ K := by
      rw [hMK]
      exact hx
    have hxS : x * s * x⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 (M ⊓ H) ⟨hxMK.1, hKH hxMK.2⟩) s).mp hs
    rw [← hSK]
    refine ⟨S.mul_mem hxS (S.inv_mem hs), ?_⟩
    have h1 : s * x⁻¹ * s⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hSN hs) _).mp (K.inv_mem hxMK.2)
    have h2 := K.mul_mem hxMK.2 h1
    simpa [mul_assoc] using h2
  set Ub := modO2Image K (T ⊓ K) with hUb
  have hU : IsSylowTwoOf Ub ⊤ := Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTK
  have hNU : Subgroup.normalizer (Ub : Set (O2Q K)) ≤ modO2Image K Bk :=
    normalizer_modO2Image_le hTK.1 hOS le_rfl
  have hKG : ∀ s (hs : s ∈ S), (∃ yb : O2Q K, alphaHom K ⟨s, hSN hs⟩ = MulAut.conj yb) ∨
      (LieModel (O2Q K) .PSL 3 2 2 ∧
        (∃ yb : O2Q K, alphaHom K ⟨s, hSN hs⟩ ^ 2 = MulAut.conj yb) ∧
        ∀ P : Subgroup (O2Q K), Subgroup.normalizer (Ub : Set (O2Q K)) ≤ P → P ⋖ ⊤ →
          P.map (alphaHom K ⟨s, hSN hs⟩).toMonoidHom ≠ P) := by
    intro s hs
    obtain ⟨e, he⟩ := hS2 ⟨s, hs⟩
    have he' : (⟨s, hSN hs⟩ : ↥(Subgroup.normalizer (K : Set G))).val ^ 2 ^ e = 1 := by
      have := congrArg Subtype.val he
      simpa using this
    refine hG (O2Q K) k hk htype Ub hU _ ⟨e, alphaHom_pow_eq_one _ he'⟩
      (map_alphaOf_modO2Image _ (hSTK hs)) fun xb hxb => ?_
    obtain ⟨x, hx, rfl⟩ := hNU hxb
    show alphaHom K ⟨s, hSN hs⟩ (QuotientGroup.mk x) * (QuotientGroup.mk x)⁻¹ ∈ Ub
    rw [alphaHom_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    refine ⟨_, ?_, rfl⟩
    show s * (x : G) * s⁻¹ * (x : G)⁻¹ ∈ T ⊓ K
    have h1 := (T ⊓ K).inv_mem (hcomm x (Subgroup.mem_subgroupOf.mp hx) s hs)
    simpa [mul_assoc] using h1
  have hinner : ∀ s (hs : s ∈ S), (∃ yb : O2Q K, alphaHom K ⟨s, hSN hs⟩ = MulAut.conj yb) →
      (∀ Q : Subgroup G, Bk ≤ Q → Q ≤ K → s ∈ Subgroup.normalizer (Q : Set G)) ∧
        s ∈ K ⊔ pCoreOf 2 H := by
    rintro s hs ⟨yb, hyb⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
    have hc := forall_comm_of_alphaHom_eq_conj _ y hyb
    have hcT := mem_normalizer_of_forall_comm hOS inf_le_right hc
    have hyB : (y : G) ∈ Bk := by
      refine ⟨y.2, ?_⟩
      have := (Subgroup.normalizer _).mul_mem (hSTK hs) (Subgroup.inv_mem _ hcT)
      simpa using this
    have hsy : s = y * ((y : G)⁻¹ * s) := by group
    refine ⟨fun Q hBQ hQK => ?_, ?_⟩
    · rw [hsy]
      exact (Subgroup.normalizer _).mul_mem (Subgroup.le_normalizer (hBQ hyB))
        (mem_normalizer_of_forall_comm (hOB.trans hBQ) hQK hc)
    · have hcH : (y : G)⁻¹ * s ∈ H := H.mul_mem (H.inv_mem (hKH y.2)) (hSH hs)
      rw [hsy]
      exact (K ⊔ pCoreOf 2 H).mul_mem (Subgroup.mem_sup_left y.2)
        (mem_sup_pCoreOf_of_forall_comm hKH hKN hTH.2.1 hTHK hcH hc)
  by_cases hall : ∀ s (hs : s ∈ S), ∃ yb : O2Q K, alphaHom K ⟨s, hSN hs⟩ = MulAut.conj yb
  · exact Or.inl fun P hP s hs => (hinner s hs (hall s hs)).1 P hP.1.le hP.2.1
  push Not at hall
  obtain ⟨s₀, hs₀, hnot⟩ := hall
  rcases hKG s₀ hs₀ with hin | ⟨hL34, ⟨y₂, hy₂⟩, hmove⟩
  · obtain ⟨yb, hyb⟩ := hin
    exact absurd hyb (hnot yb)
  refine Or.inr ⟨hL34, ?_, fun P hP hBP hSP => ?_⟩
  swap
  ·
    have hPm : IsMaxParabolicOver K (T ⊓ K) P :=
      ⟨hP.1.1, hBP, hP.2.1, fun Q hPQ hQK hQne =>
        hP.2.2 Q ⟨hQK, T ⊓ K, hTK, hBP.trans hPQ⟩ hQne hPQ⟩
    obtain ⟨hN, hcov⟩ := hPm.modO2Image_spec hTK.1 hOS
    exact hmove _ hN hcov (map_alphaOf_modO2Image _ (hSP hs₀))
  set N₀ := K ⊔ pCoreOf 2 H with hN₀
  have hOT : pCoreOf 2 H ≤ T := F7.isSylowTwoOf_pCoreOf_le hTH
  have hOH : pCoreOf 2 H ≤ S :=
    le_pCoreOf_of_le_normalizer 2 (le_inf (hOT.trans h.T_le) (pCoreOf_le 2 H))
      (inf_le_right.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  have hN₀H : H ≤ Subgroup.normalizer (N₀ : Set G) :=
    F1.le_normalizer_sup hKN (le_normalizer_pCoreOf 2 H)
  obtain ⟨Pj, -, hiff, hj, -⟩ := hF (O2Q K) k hk htype Ub hU
  have hP0 : Subgroup.normalizer (Ub : Set (O2Q K)) ≤ Pj 0 := (hj 0).1.le
  have hP0c : Pj 0 ⋖ ⊤ := (hiff _ hP0).mpr ⟨0, rfl⟩
  have hswap : ∀ s (hs : s ∈ S), ¬ (∃ yb : O2Q K, alphaHom K ⟨s, hSN hs⟩ = MulAut.conj yb) →
      (Pj 0).map (alphaHom K ⟨s, hSN hs⟩).toMonoidHom = Pj 1 := by
    intro s hs hns
    rcases hKG s hs with hin | ⟨-, -, hmv⟩
    · exact absurd hin hns
    obtain ⟨hN', hc'⟩ :=
      covBy_map_of_map_eq (map_alphaOf_modO2Image ⟨s, hSN hs⟩ (hSTK hs)) hP0 hP0c
    obtain ⟨j, hj'⟩ := (hiff _ hN').mp hc'
    have hj1 : j = 1 := by
      fin_cases j
      · exact absurd hj' (hmv _ hP0 hP0c)
      · rfl
    rw [hj', hj1]
  have hcls : ∀ s ∈ S, s ∈ N₀ ∨ s₀⁻¹ * s ∈ N₀ := by
    intro s hs
    by_cases hin : ∃ yb : O2Q K, alphaHom K ⟨s, hSN hs⟩ = MulAut.conj yb
    · exact Or.inl (hinner s hs hin).2
    · right
      have hs' : s₀⁻¹ * s ∈ S := S.mul_mem (S.inv_mem hs₀) hs
      have hα : alphaHom K ⟨s₀⁻¹ * s, hSN hs'⟩ =
          (alphaHom K ⟨s₀, hSN hs₀⟩)⁻¹ * alphaHom K ⟨s, hSN hs⟩ := by
        rw [← map_inv, ← map_mul]
        rfl
      have hfix : (Pj 0).map (alphaHom K ⟨s₀⁻¹ * s, hSN hs'⟩).toMonoidHom = Pj 0 := by
        rw [hα, map_mulAut_mul, hswap s hs hin,
          ← hswap s₀ hs₀ (fun ⟨yb, hh⟩ => hnot yb hh), map_mulAut_inv_map]
      rcases hKG _ hs' with hin' | ⟨-, -, hmv⟩
      · exact (hinner _ hs' hin').2
      · exact absurd hfix (hmv _ hP0 hP0c)
  have hs₀sq : s₀ * s₀ ∈ N₀ := by
    have hs' : s₀ * s₀ ∈ S := S.mul_mem hs₀ hs₀
    refine (hinner _ hs' ⟨y₂, ?_⟩).2
    rw [← hy₂, pow_two, ← map_mul]
    rfl
  have hs₀N : s₀ ∉ N₀ := by
    intro hs₀N
    have hON : pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) := (pCoreOf_le 2 H).trans hKN
    obtain ⟨k₀, hk₀, o, ho, hko⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hON).mp hs₀N
    have hoc : ∀ x ∈ K, o * x * o⁻¹ * x⁻¹ ∈ pCoreOf 2 K := by
      intro x hx
      have h1 : o * x * o⁻¹ * x⁻¹ ∈ K :=
        K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hON ho) x).mp hx) (K.inv_mem hx)
      have h2 : o * x * o⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
        have h3 := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_pCoreOf 2 H (hKH hx)) _).mp (Subgroup.inv_mem _ ho)
        have h4 := (pCoreOf 2 H).mul_mem ho h3
        simpa [mul_assoc] using h4
      have hn : K ≤ Subgroup.normalizer ((K ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
        fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hy, le_normalizer_pCoreOf 2 H (hKH hy)⟩
      exact le_pCoreOf_of_le_normalizer 2 inf_le_left hn
        ((pCoreOf_isPGroup 2 H).to_le inf_le_right) ⟨h1, h2⟩
    set Q := ((Pj 0).comap π).map K.subtype with hQ
    have hQK : Q ≤ K := Subgroup.map_subtype_le _
    have hBQ : Bk ≤ Q := by
      intro x hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      show π ⟨x, hx.1⟩ ∈ Pj 0
      exact hP0 (Vol2.Ch11.SecS.modO2Image_le_normalizer (A := T ⊓ K) (B := Bk) inf_le_right
        ⟨⟨x, hx.1⟩, hx, rfl⟩)
    have hk₀B : k₀ ∈ Bk := by
      refine ⟨hk₀, ?_⟩
      have hoT : o ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer (hOT ho), hON ho⟩
      have := (Subgroup.normalizer _).mul_mem (hSTK hs₀) (Subgroup.inv_mem _ hoT)
      rwa [hko, mul_inv_cancel_right] at this
    have hs₀Q : s₀ ∈ Subgroup.normalizer (Q : Set G) := by
      rw [hko]
      exact (Subgroup.normalizer _).mul_mem (Subgroup.le_normalizer (hBQ hk₀B))
        (mem_normalizer_of_forall_comm (hOB.trans hBQ) hQK hoc)
    have hQb : modO2Image K Q = Pj 0 := by
      unfold modO2Image
      rw [hQ, show (((Pj 0).comap π).map K.subtype).subgroupOf K = (Pj 0).comap π from
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective _,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
    have h1 := map_alphaOf_modO2Image ⟨s₀, hSN hs₀⟩ hs₀Q
    rw [hQb] at h1
    exact hmove _ hP0 hP0c h1
  have hX : ∀ x ∈ K ⊔ S, ∃ k ∈ K, ∃ s ∈ S, x = k * s := fun x hx =>
    (F1.mem_sup_iff_exists_mul_of_normalizes hSN).mp hx
  have hN₀X : N₀ ≤ K ⊔ S := sup_le le_sup_left (hOH.trans le_sup_right)
  have hs₀X : s₀ ∈ K ⊔ S := Subgroup.mem_sup_right hs₀
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨s₀, hs₀X⟩, fun ⟨x, hx⟩ => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  obtain ⟨k, hk, s, hs, rfl⟩ := hX x hx
  have hkN : k ∈ N₀ := Subgroup.mem_sup_left hk
  have hiff1 : k * s ∈ N₀ ↔ s ∈ N₀ :=
    ⟨fun h1 => by simpa using N₀.mul_mem (N₀.inv_mem hkN) h1, fun h1 => N₀.mul_mem hkN h1⟩
  have hiff2 : k * s * s₀ ∈ N₀ ↔ s * s₀ ∈ N₀ :=
    ⟨fun h1 => by simpa [mul_assoc] using N₀.mul_mem (N₀.inv_mem hkN) h1,
      fun h1 => by simpa [mul_assoc] using N₀.mul_mem hkN h1⟩
  rw [hiff1, hiff2]
  by_cases hsN : s ∈ N₀
  · refine Or.inr ⟨hsN, fun h2 => hs₀N ?_⟩
    simpa using N₀.mul_mem (N₀.inv_mem hsN) h2
  · have h1 : s₀⁻¹ * s ∈ N₀ := (hcls s hs).resolve_left hsN
    refine Or.inl ⟨?_, hsN⟩
    have h3 := N₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hN₀H (hSH hs₀)) _).mp h1) hs₀sq
    have h4 : s₀ * (s₀⁻¹ * s) * s₀⁻¹ * (s₀ * s₀) = s * s₀ := by group
    rwa [h4] at h3

end CFSG.Quasithin.H13
