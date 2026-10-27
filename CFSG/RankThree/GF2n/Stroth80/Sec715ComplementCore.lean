module

public import CFSG.RankThree.GF2n.Stroth80.Sec715OddComplement
public import CFSG.RankThree.GF2n.Stroth80.Sec715TorusFree

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sec715Torus

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalGroups.F2Fixed
open CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

structure ExtData (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) (M₀ M : Type)
    [AddCommGroup M₀] [Finite M₀] [DistribMulAction (Gom (quadPlus n K)) M₀]
    [AddCommGroup M] [Finite M] [DistribMulAction (Gom (quadPlus n K)) M]
    (V₀ : AddSubgroup M) (π : M →+ M₀) (P : HypPair (quadPlus n K)) : Prop where
  two₀ : ∀ m : M₀, m + m = 0
  two : ∀ m : M, m + m = 0
  fixed : ∀ (g : Gom (quadPlus n K)) (v : M), v ∈ V₀ → g • v = v
  ker : ∀ m : M, π m = 0 ↔ m ∈ V₀
  equiv : ∀ (g : Gom (quadPlus n K)) (m : M), π (g • m) = g • π m
  surj : Function.Surjective π
  irr : ∀ W : AddSubgroup M₀, (∀ (g : Gom (quadPlus n K)) (x : M₀), x ∈ W → g • x ∈ W) →
    W = ⊥ ∨ W = ⊤
  nontrivial : Nontrivial M₀
  dec : IsCompl (fixedSub M₀ (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))))
    (fixedSub M₀ (Lom (quadPlus n K) P.f : Set (Gom (quadPlus n K))))

section ExtData

variable {M₀ M : Type} [AddCommGroup M₀] [Finite M₀] [DistribMulAction (Gom (quadPlus n K)) M₀]
  [AddCommGroup M] [Finite M] [DistribMulAction (Gom (quadPlus n K)) M]
  {V₀ : AddSubgroup M} {π : M →+ M₀} {P : HypPair (quadPlus n K)}

theorem ExtData.swap (H : ExtData K n M₀ M V₀ π P) : ExtData K n M₀ M V₀ π (pairSwap P) :=
  ⟨H.two₀, H.two, H.fixed, H.ker, H.equiv, H.surj, H.irr, H.nontrivial, H.dec.symm⟩

theorem ExtData.dec_map (H : ExtData K n M₀ M V₀ π P) (g : Gom (quadPlus n K)) :
    IsCompl (fixedSub M₀ (Lom (quadPlus n K) (g.app P.e) : Set (Gom (quadPlus n K))))
      (fixedSub M₀ (Lom (quadPlus n K) (g.app P.f) : Set (Gom (quadPlus n K)))) := by
  have := isCompl_fixedSub_conj g H.dec
  rwa [image_conj_Lom, image_conj_Lom] at this

theorem ExtData.fixedSub_torus (H : ExtData K n M₀ M V₀ π P) (hK : 2 < Nat.card K)
    (hn : 4 ≤ n) (R : HypPair (quadPlus n K)) {s : K} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    fixedSub M {torusG (by omega) R hs} = V₀ := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨g, hge, hgf⟩ : ∃ g : Gom (quadPlus n K), g.app P.e = R.e ∧ g.app P.f = R.f :=
    exists_gom_pair (nondegenerate_polarBilin_quadPlus n K)
      (plusPair_orth (K := K) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
      P.Q_e P.Q_f R.Q_e R.Q_f P.polar_ef R.polar_ef
  have hdec := H.dec_map g
  rw [hge, hgf] at hdec
  haveI := H.nontrivial
  have hfix := torus_fixedSub_eq_bot hK hn H.two₀ H.irr R hdec hs hs1
  refine le_antisymm (fun m hm => ?_) (fun v hv t ht => ?_)
  · have h1 : π m ∈ fixedSub M₀ {torusG (by omega) R hs} := by
      intro t ht
      rw [Set.mem_singleton_iff.mp ht, ← H.equiv, hm _ rfl]
    rw [hfix, AddSubgroup.mem_bot] at h1
    exact (H.ker m).mp h1
  · rw [Set.mem_singleton_iff.mp ht]
    exact H.fixed _ v hv

theorem smul_comm_apply {Γ : Type*} [Group Γ] {N : Type*} [AddCommGroup N]
    [DistribMulAction Γ N] (g τ : Γ) (m : N) :
    g • comm N τ m = comm N (g * τ * g⁻¹) (g • m) := by
  simp only [comm_apply, smul_sub, mul_smul, inv_smul_smul]

theorem ExtData.range_comm_torus_eq (H : ExtData K n M₀ M V₀ π P) (hK : 2 < Nat.card K)
    (hn : 4 ≤ n) (R₁ R₂ : HypPair (quadPlus n K)) {s₁ s₂ : K} (hs₁ : s₁ ≠ 0) (hs₁1 : s₁ ≠ 1)
    (hs₂ : s₂ ≠ 0) (hs₂1 : s₂ ≠ 1)
    (hcomm : torusG (by omega) R₁ hs₁ * torusG (by omega) R₂ hs₂ =
      torusG (by omega) R₂ hs₂ * torusG (by omega) R₁ hs₁) :
    (comm M (torusG (by omega) R₁ hs₁)).range = (comm M (torusG (by omega) R₂ hs₂)).range :=
  sec715_range_comm_eq_of_commute H.two (torusG_pow _ R₁ hs₁) odd_card_sub_one_of_charTwo
    (torusG_pow _ R₂ hs₂) odd_card_sub_one_of_charTwo hcomm
    ((H.fixedSub_torus hK hn R₁ hs₁ hs₁1).trans (H.fixedSub_torus hK hn R₂ hs₂ hs₂1).symm)

theorem ExtData.smul_mem_range_torus (H : ExtData K n M₀ M V₀ π P) (hK : 2 < Nat.card K)
    (hn : 4 ≤ n) (R R₂ : HypPair (quadPlus n K)) {s s₂ : K} (hs : s ≠ 0) (hs1 : s ≠ 1)
    (hs₂ : s₂ ≠ 0) (hs₂1 : s₂ ≠ 1) (g : Gom (quadPlus n K))
    (h1 : torusG (by omega) R hs * torusG (by omega) R₂ hs₂ =
      torusG (by omega) R₂ hs₂ * torusG (by omega) R hs)
    (h2 : torusG (by omega) (pairMap R g) hs * torusG (by omega) R₂ hs₂ =
      torusG (by omega) R₂ hs₂ * torusG (by omega) (pairMap R g) hs)
    {y : M} (hy : y ∈ (comm M (torusG (by omega) R hs)).range) :
    g • y ∈ (comm M (torusG (by omega) R hs)).range := by
  obtain ⟨m, rfl⟩ := hy
  rw [smul_comm_apply, torusG_conj]
  have e1 := H.range_comm_torus_eq hK hn R R₂ hs hs1 hs₂ hs₂1 h1
  have e2 := H.range_comm_torus_eq hK hn (pairMap R g) R₂ hs hs1 hs₂ hs₂1 h2
  rw [e1, ← e2]
  exact ⟨_, rfl⟩

theorem invariant_of_closure {Γ : Type*} [Group Γ] {N : Type*} [AddCommGroup N]
    [DistribMulAction Γ N] (Y : AddSubgroup N) (S : Set Γ)
    (h : ∀ l ∈ S, (∀ y ∈ Y, l • y ∈ Y) ∧ (∀ y ∈ Y, l⁻¹ • y ∈ Y)) :
    ∀ l ∈ Subgroup.closure S, ∀ y ∈ Y, l • y ∈ Y := by
  intro l hl
  have key : (∀ y ∈ Y, l • y ∈ Y) ∧ (∀ y ∈ Y, l⁻¹ • y ∈ Y) := by
    induction hl using Subgroup.closure_induction with
    | mem x hx => exact h x hx
    | one => exact ⟨fun y hy => by simpa using hy, fun y hy => by simpa using hy⟩
    | mul a b _ _ iha ihb =>
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · rw [mul_smul]
        exact iha.1 _ (ihb.1 y hy)
      · rw [mul_inv_rev, mul_smul]
        exact ihb.2 _ (iha.2 y hy)
    | inv a _ iha => exact ⟨iha.2, fun y hy => by simpa using iha.1 y hy⟩
  exact key.1

theorem ExtData.exists_complement_std (hK : 2 < Nat.card K) (hn : 4 ≤ n)
    (H : ExtData K n M₀ M V₀ π (plusPair K (⟨0, by omega⟩ : Fin n))) :
    ∃ Y : AddSubgroup M, IsCompl Y V₀ ∧
      ∀ l ∈ Lom (quadPlus n K) (plusPair K (⟨0, by omega⟩ : Fin n)).e, ∀ y ∈ Y, l • y ∈ Y := by
  have hn3 : 3 ≤ n := by omega
  have hQ := nondegenerate_polarBilin_quadPlus n K
  obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_ne hK 1
  set P := plusPair K (⟨0, by omega⟩ : Fin n) with hP
  set P1 := plusPair K (⟨1, by omega⟩ : Fin n) with hP1
  set R := plusPair K (⟨2, by omega⟩ : Fin n) with hR
  have o01 : P.Orth P1 := plusPair_orth (by simp [Fin.ext_iff])
  have o02 : P.Orth R := plusPair_orth (by simp [Fin.ext_iff])
  have o12 : P1.Orth R := plusPair_orth (by simp [Fin.ext_iff])
  set τ := torusG hn3 P hs0 with hτ
  set b₀ : Fin n ⊕ Fin n → K := P1.e + P1.f with hb₀
  have hb₀Pe : polar (quadPlus n K) P.e b₀ = 0 := by
    rw [hb₀, polar_add_right, o01.ee, o01.ef, add_zero]
  have hb₀Pf : polar (quadPlus n K) P.f b₀ = 0 := by
    rw [hb₀, polar_add_right, o01.fe, o01.ff, add_zero]
  have hb₀Re : polar (quadPlus n K) R.e b₀ = 0 := by
    rw [hb₀, polar_add_right, o12.symm.ee, o12.symm.ef, add_zero]
  have hb₀Rf : polar (quadPlus n K) R.f b₀ = 0 := by
    rw [hb₀, polar_add_right, o12.symm.fe, o12.symm.ff, add_zero]
  have hb₀Re' : polar (quadPlus n K) b₀ R.e = 0 := by rw [polar_comm]; exact hb₀Re
  have hb₀Rf' : polar (quadPlus n K) b₀ R.f = 0 := by rw [polar_comm]; exact hb₀Rf
  have hQb₀ : (quadPlus n K) b₀ = 1 := by
    rw [hb₀, QuadraticMap.map_add (quadPlus n K) P1.e P1.f, P1.Q_e, P1.Q_f, P1.polar_ef]
    simp
  set Y : AddSubgroup M := (comm M τ).range with hY
  have hfix : fixedSub M {τ} = V₀ := H.fixedSub_torus hK hn P hs0 hs1
  have hcompl : IsCompl Y V₀ := by
    have := sec715_isCompl_range_comm_fixedSub H.two τ (torusG_pow hn3 P hs0)
      odd_card_sub_one_of_charTwo
    rwa [hfix] at this
  refine ⟨Y, hcompl, ?_⟩
  have hinvg : ∀ g : Gom (quadPlus n K), g.app P.e = P.e → g.app P.f = P.f →
      ∀ y ∈ Y, g • y ∈ Y := by
    intro g hge hgf y hy
    obtain ⟨m, rfl⟩ := hy
    have hc := torusG_comm_of_fixed hn3 P hs0 hge hgf
    rw [smul_comm_apply]
    have e1 : g * τ * g⁻¹ = τ := by
      rw [hτ, hc]
      group
    rw [e1]
    exact ⟨_, rfl⟩
  have hinvx : ∀ c : K, ∀ y ∈ Y, eichlerG (quadPlus n K) P.e (c • b₀) • y ∈ Y := by
    intro c y hy
    have hcb : polar (quadPlus n K) P.e (c • b₀) = 0 := by
      rw [polar_smul_right_eq, hb₀Pe, mul_zero]
    set x := eichlerG (quadPlus n K) P.e (c • b₀) with hx
    have hxe : x.app P.e = P.e := by
      rw [hx, eichlerG_app P.Q_e hcb, P.polar_ee, hcb]
      simp
    have hxf : x.app P.f = P.f + c • b₀ - ((quadPlus n K) (c • b₀)) • P.e := by
      rw [hx, eichlerG_app P.Q_e hcb, P.polar_fe, polar_smul_right_eq, hb₀Pf]
      simp
    have hperpR : ∀ v : Fin n ⊕ Fin n → K, polar (quadPlus n K) v R.e = 0 →
        polar (quadPlus n K) v R.f = 0 → (torusG hn3 R hs0).app v = v := fun v h1 h2 =>
      torusLin_app_of_perp R s h1 h2
    have h1 : τ * torusG hn3 R hs0 = torusG hn3 R hs0 * τ :=
      torusG_comm_of_fixed hn3 R hs0 (g := τ)
        (torusLin_app_of_perp P s o02.symm.ee o02.symm.ef)
        (torusLin_app_of_perp P s o02.symm.fe o02.symm.ff)
    have h2 : torusG hn3 (pairMap P x) hs0 * torusG hn3 R hs0 =
        torusG hn3 R hs0 * torusG hn3 (pairMap P x) hs0 := by
      refine (torusG_comm_of_fixed hn3 (pairMap P x) hs0 (g := torusG hn3 R hs0) ?_ ?_).symm
      · show (torusG hn3 R hs0).app (x.app P.e) = x.app P.e
        rw [hxe]
        exact hperpR _ o02.ee o02.ef
      · show (torusG hn3 R hs0).app (x.app P.f) = x.app P.f
        rw [hxf]
        refine hperpR _ ?_ ?_
        · simp only [polar_add_left, polar_sub_left, polar_smul_left_eq, o02.fe, o02.ee,
            polar_smul_left_eq, hb₀Re']
          ring
        · simp only [polar_add_left, polar_sub_left, polar_smul_left_eq, o02.ff, o02.ef,
            polar_smul_left_eq, hb₀Rf']
          ring
    exact H.smul_mem_range_torus hK hn P R hs0 hs1 hs0 hs1 x h1 h2 hy
  have hgen : ∀ b : Fin n ⊕ Fin n → K, polar (quadPlus n K) P.e b = 0 →
      polar (quadPlus n K) P.f b = 0 → (quadPlus n K) b ≠ 0 →
      ∀ y ∈ Y, eichlerG (quadPlus n K) P.e b • y ∈ Y := by
    intro b hbe hbf hQb y hy
    obtain ⟨c, hc⟩ := isSquare_of_charTwo' ((quadPlus n K) b)
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hQb
      rw [hc]
      ring
    have hW := HypPair.polarNondegOn_perp hQ P
    have hP1e : P1.e ∈ P.perp := HypPair.mem_perp.mpr ⟨o01.ee, o01.fe⟩
    have hP1f : P1.f ∈ P.perp := HypPair.mem_perp.mpr ⟨o01.ef, o01.ff⟩
    have hRe : R.e ∈ P.perp := HypPair.mem_perp.mpr ⟨o02.ee, o02.fe⟩
    have hRf : R.f ∈ P.perp := HypPair.mem_perp.mpr ⟨o02.ef, o02.ff⟩
    have hb₁W : c • b₀ ∈ P.perp := P.perp.smul_mem c (P.perp.add_mem hP1e hP1f)
    have hbW : b ∈ P.perp := HypPair.mem_perp.mpr ⟨hbe, hbf⟩
    have hQeq : (quadPlus n K) (c • b₀) = (quadPlus n K) b := by
      rw [map_smul_eq_sq, hQb₀, hc]
      ring
    have hb₁0 : c • b₀ ≠ 0 := by
      intro h
      apply hQb
      rw [← hQeq, h, QuadraticMap.map_zero]
    have hbne : b ≠ 0 := fun h => hQb (by rw [h, QuadraticMap.map_zero])
    obtain ⟨g, hg, hgx, -, hgz⟩ := exists_mem_elementaryGroup_apply_eq_of_mem hW o12 hP1e hP1f
      hRe hRf hb₁W hbW hb₁0 hbne hQeq
    let g' : Gom (quadPlus n K) := ⟨g, hg⟩
    have hg'e : g'.app P.e = P.e := hgz P.e (fun w hw => (HypPair.mem_perp.mp hw).1)
    have hg'f : g'.app P.f = P.f := hgz P.f (fun w hw => (HypPair.mem_perp.mp hw).2)
    have hg'b : g'.app (c • b₀) = b := hgx
    have hgie : g'⁻¹.app P.e = P.e := by
      have := Gom.app_inv_app g' P.e
      rwa [hg'e] at this
    have hgif : g'⁻¹.app P.f = P.f := by
      have := Gom.app_inv_app g' P.f
      rwa [hg'f] at this
    have e1 : eichlerG (quadPlus n K) P.e b =
        g' * eichlerG (quadPlus n K) P.e (c • b₀) * g'⁻¹ := by
      rw [eichlerG_conj, hg'e, hg'b]
    rw [e1, mul_smul, mul_smul]
    exact hinvg g' hg'e hg'f _ (hinvx c _ (hinvg g'⁻¹ hgie hgif y hy))
  intro l hl
  have hef : polar (quadPlus n K) P.f P.e ≠ 0 := by
    rw [P.polar_fe]
    exact one_ne_zero
  have hcl := Lom_le_closure_eichlerNonA2Set hQ P.Q_f P.Q_e hef hK hl
  refine invariant_of_closure Y (eichlerNonA2Set (quadPlus n K) P.f P.e) ?_ l hcl
  rintro a ⟨w, hfw, hew, hQw, rfl⟩
  have hinv := hgen w hew hfw hQw
  have hinvinv : (eichlerG (quadPlus n K) P.e w)⁻¹ = eichlerG (quadPlus n K) P.e w :=
    inv_eq_of_mul_eq_one_right (eichlerG_mul_self hew)
  refine ⟨hinv, ?_⟩
  rw [hinvinv]
  exact hinv

theorem ExtData.exists_complement (hK : 2 < Nat.card K) (hn : 4 ≤ n)
    (H : ExtData K n M₀ M V₀ π P) :
    ∃ Y : AddSubgroup M, IsCompl Y V₀ ∧
      ∀ l ∈ Lom (quadPlus n K) P.e, ∀ y ∈ Y, l • y ∈ Y := by
  obtain ⟨g, hge, hgf⟩ : ∃ g : Gom (quadPlus n K),
      g.app P.e = (plusPair K (⟨0, by omega⟩ : Fin n)).e ∧
      g.app P.f = (plusPair K (⟨0, by omega⟩ : Fin n)).f :=
    exists_gom_pair (nondegenerate_polarBilin_quadPlus n K)
      (plusPair_orth (K := K) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
      P.Q_e P.Q_f (plusPair K (⟨0, by omega⟩ : Fin n)).Q_e
      (plusPair K (⟨0, by omega⟩ : Fin n)).Q_f P.polar_ef
      (plusPair K (⟨0, by omega⟩ : Fin n)).polar_ef
  have hdec := H.dec_map g
  rw [hge, hgf] at hdec
  have H0 : ExtData K n M₀ M V₀ π (plusPair K (⟨0, by omega⟩ : Fin n)) :=
    ⟨H.two₀, H.two, H.fixed, H.ker, H.equiv, H.surj, H.irr, H.nontrivial, hdec⟩
  obtain ⟨Y₀, hY₀, hinv⟩ := H0.exists_complement_std hK hn
  refine ⟨Y₀.map (DistribSMul.toAddMonoidHom M g⁻¹), ⟨?_, ?_⟩, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨y₀, hy₀, rfl⟩ := AddSubgroup.mem_map.mp hy1
    have hv : g⁻¹ • y₀ ∈ V₀ := hy2
    have h1 : y₀ = g⁻¹ • y₀ := by
      have := H.fixed g _ hv
      rwa [smul_inv_smul] at this
    have h2 : y₀ ∈ Y₀ ⊓ V₀ := ⟨hy₀, by rw [h1]; exact hv⟩
    rw [hY₀.inf_eq_bot, AddSubgroup.mem_bot] at h2
    rw [AddSubgroup.mem_bot]
    show g⁻¹ • y₀ = 0
    rw [h2, smul_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro m _
    have hm : g • m ∈ Y₀ ⊔ V₀ := by rw [hY₀.sup_eq_top]; trivial
    obtain ⟨y₀, hy₀, v, hv, hyv⟩ := AddSubgroup.mem_sup.mp hm
    have : m = g⁻¹ • y₀ + v := by
      have h1 : g⁻¹ • (g • m) = g⁻¹ • (y₀ + v) := by rw [hyv]
      rw [inv_smul_smul, smul_add, H.fixed g⁻¹ v hv] at h1
      exact h1
    rw [this]
    exact AddSubgroup.add_mem_sup (AddSubgroup.mem_map.mpr ⟨y₀, hy₀, rfl⟩) hv
  · intro l hl y hy
    obtain ⟨y₀, hy₀, rfl⟩ := AddSubgroup.mem_map.mp hy
    have hconj : g * l * g⁻¹ ∈ Lom (quadPlus n K) (plusPair K (⟨0, by omega⟩ : Fin n)).e := by
      have := conj_mem_Lom g hl
      rwa [hge] at this
    refine AddSubgroup.mem_map.mpr ⟨(g * l * g⁻¹) • y₀, hinv _ hconj y₀ hy₀, ?_⟩
    show g⁻¹ • (g * l * g⁻¹) • y₀ = l • g⁻¹ • y₀
    simp only [mul_smul, inv_smul_smul]

end ExtData

end CFSG.RankThree.GF2n.Stroth80.Sec715Torus
