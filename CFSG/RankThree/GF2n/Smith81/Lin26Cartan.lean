module

public import CFSG.RankThree.GF2n.Smith81.Lin26Torus

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Pointwise Matrix

section Homology

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}
  {n : ℕ} {V₁ V₂ : Subgroup G}

structure IsHomology {K : Type} [Field K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (M : Subgroup G) (W : Submodule K M₀.E) (k : G) (ν : Kˣ) (f : M₀.E →ₗ[K] M₀.E)
    (b : M₀.E) : Prop where
  mem : k ∈ M
  act : ∀ x ∈ Q, M₀.π (k * x * k⁻¹) = f (M₀.π x)
  mult : ∀ z ∈ Z, γ (k * z * k⁻¹) = (ν : K) * γ z
  qf : ∀ e, M₀.Qf (f e) = (ν : K) * M₀.Qf e
  b_mem : b ∈ W
  b_ne : b ≠ 0
  fb : f b = ((ν⁻¹ : Kˣ) : K) • b
  hom : ∀ w ∈ W, f w - w ∈ Submodule.span K {b}

theorem RestModel.homology_of_torus (R : RestModel M Q Z n V₁ V₂) (hn : 2 ≤ n) {Y : Subgroup G}
    (hY : Ctx M Q Z Y) (hYV : Y ≤ V₂) (hmod : V₂ ≤ QB Y) {x : G} (hxX : x ∈ Q ⊔ QB Y)
    (hxZ : x ∈ Subgroup.normalizer (Z : Set G)) (hxY : x ∈ Subgroup.normalizer (Y : Set G)) :
    ∃ (ν : R.Kˣ) (f : R.M₀.E →ₗ[R.K] R.M₀.E) (b : R.M₀.E), IsHomology R.M₀ M R.W₂ x ν f b := by
  classical
  have H := R.hyp
  have hxM : x ∈ M := by rw [← H.normalizer_Z.1]; exact hxZ
  obtain ⟨σ, a, T, hT1, hTπ, hTγ, hTQ⟩ := R.gm.act x hxM
  obtain ⟨b, hb0, -, hbY, -, -⟩ := hY.dictB R.gm
  have hYQ : Y ≤ Q := hY.le
  have hbY1 : b ∈ R.M₀.img Y := (hbY b).mpr ⟨1, (one_smul _ _).symm⟩
  have hbW : b ∈ R.W₂ := (R.memW₂ b).mpr (R.M₀.img_mono hYV hbY1)
  have hTY : ∀ v ∈ R.M₀.img Y, T v ∈ R.M₀.img Y := by
    rintro _ ⟨y, hyY, hyQ, rfl⟩
    rw [← hTπ y hyQ]
    exact R.M₀.pi_mem_img ((Subgroup.mem_normalizer_iff.mp hxY y).mp hyY) (conj_mem_Q H hxM hyQ)
  obtain ⟨ρ, hρ⟩ := (hbY _).mp (hTY b hbY1)
  have hdiff : ∀ w ∈ R.W₂, T w - w ∈ Submodule.span R.K {b} := by
    intro w hw
    obtain ⟨v, hvV, hvQ, rfl⟩ := (R.memW₂ w).mp hw
    have hvD : v ∈ Q ⊓ QB Y := ⟨hvQ, hmod hvV⟩
    have hc := Ctx.sup_QB_comm_inf_mem hY hxX hvD
    obtain ⟨z, hz, y', hy', hzy⟩ := (Ctx.mem_sup_iff hY).mp hc
    have hzQ : z ∈ Q := H.Z_normal.1 hz
    have hy'Q : y' ∈ Q := hYQ hy'
    have e1 : x * v * x⁻¹ = ⁅x, v⁆ * v := by simp only [commutatorElement_def]; group
    have h1 : R.M₀.π (x * v * x⁻¹) = R.M₀.π ⁅x, v⁆ + R.M₀.π v := by
      rw [e1]; exact R.M₀.π_mul _ (by rw [hzy]; exact Q.mul_mem hzQ hy'Q) v hvQ
    have h2 : R.M₀.π ⁅x, v⁆ = R.M₀.π y' := by
      rw [hzy, R.M₀.π_mul z hzQ y' hy'Q, (R.M₀.π_ker z hzQ).mpr hz, zero_add]
    obtain ⟨s, hs⟩ := (hbY _).mp (R.M₀.pi_mem_img hy' hy'Q)
    rw [← hTπ v hvQ, h1, h2, add_sub_cancel_right, hs]
    exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self b)
  have hex : ∃ w ∈ R.W₂, w ∉ Submodule.span R.K {b} := by
    by_contra hcon
    push Not at hcon
    have hle : R.W₂ ≤ Submodule.span R.K {b} := hcon
    have h1 := Submodule.finrank_mono hle
    have h2 : Module.finrank R.K ↥(Submodule.span R.K {b}) = 1 := finrank_span_singleton hb0
    have h3 : Nat.card ↥R.W₂ = Nat.card R.K ^ Module.finrank R.K ↥R.W₂ :=
      Module.natCard_eq_pow_finrank
    rw [R.card_W₂, R.gm.card] at h3
    have h4 : n = Module.finrank R.K ↥R.W₂ :=
      Nat.pow_right_injective (le_trans (by norm_num) H.q4) h3
    omega
  obtain ⟨w, hwW, hwb⟩ := hex
  have hσ : ∀ c : R.K, σ c = c := by
    intro c
    by_contra hne
    have h1 : T (c • w) - c • w ∈ Submodule.span R.K {b} := hdiff _ (R.W₂.smul_mem c hwW)
    have h2 : T w - w ∈ Submodule.span R.K {b} := hdiff w hwW
    have h3 := Submodule.sub_mem _ (Submodule.smul_mem _ (σ c) h2) h1
    have h4 : σ c • (T w - w) - (T (c • w) - c • w) = (c - σ c) • w := by
      rw [hT1]; module
    rw [h4] at h3
    have hc : c - σ c ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    apply hwb
    have := Submodule.smul_mem _ (c - σ c)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  let f : R.M₀.E →ₗ[R.K] R.M₀.E :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun c e => by rw [hT1, hσ c]; rfl }
  have hfT : ∀ e, f e = T e := fun e => rfl
  have hmult : ∀ z ∈ Z, R.γ (x * z * x⁻¹) = (a : R.K) * R.γ z := fun z hz => by
    rw [hTγ z hz, hσ]
  have hqf : ∀ e, R.M₀.Qf (f e) = (a : R.K) * R.M₀.Qf e := fun e => by
    rw [hfT, hTQ, hσ]
  obtain ⟨y₀, hy₀Y, hy₀Q, hy₀b⟩ := hbY1
  obtain ⟨e', he'⟩ : ∃ e', R.M₀.B e' b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hb0 (R.M₀.nondeg b (fun f' => by rw [Tim79.QuadModel.B_comm, hcon f', neg_zero]))
  obtain ⟨g, hgQ, hg⟩ := R.M₀.π_surj e'
  have htc := Ctx.torus_comm hY hxX hxZ hxY hy₀Y hgQ
  have hZc : ⁅y₀, g⁆ ∈ Z := comm_mem_Z H hy₀Q hgQ
  have hxinvZ : ∀ z ∈ Z, x⁻¹ * z * x ∈ Z := fun z hz => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxZ) z).mp hz
    simpa using this
  have hγL : R.γ ⁅x * y₀ * x⁻¹, g⁆ = ρ * R.M₀.B b (R.M₀.π g) := by
    rw [R.M₀.comm_eq _ (conj_mem_Q H hxM hy₀Q) g hgQ, hTπ y₀ hy₀Q, hy₀b, hρ, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
  have hγR : R.γ (x⁻¹ * ⁅y₀, g⁆ * x) = (a : R.K)⁻¹ * R.γ ⁅y₀, g⁆ := by
    have h1 := hmult _ (hxinvZ _ hZc)
    have e2 : x * (x⁻¹ * ⁅y₀, g⁆ * x) * x⁻¹ = ⁅y₀, g⁆ := by group
    rw [e2] at h1
    have ha0 : (a : R.K) ≠ 0 := a.ne_zero
    field_simp
    exact h1.symm ▸ by ring
  have hγy : R.γ ⁅y₀, g⁆ = R.M₀.B b (R.M₀.π g) := by
    rw [R.M₀.comm_eq y₀ hy₀Q g hgQ, hy₀b]
  have hBne : R.M₀.B b (R.M₀.π g) ≠ 0 := by
    rw [Tim79.QuadModel.B_comm, hg]; exact neg_ne_zero.mpr he'
  have hρa : ρ = (a : R.K)⁻¹ := by
    have h1 : R.γ ⁅x * y₀ * x⁻¹, g⁆ = R.γ (x⁻¹ * ⁅y₀, g⁆ * x) := by rw [htc]
    rw [hγL, hγR, hγy] at h1
    exact mul_right_cancel₀ hBne h1
  refine ⟨a, f, b, ⟨hxM, fun x' hx' => hTπ x' hx', hmult, hqf, hbW, hb0, ?_, ?_⟩⟩
  · show T b = ((a⁻¹ : R.Kˣ) : R.K) • b
    rw [hρ, hρa, Units.val_inv_eq_inv_val]
  · intro w hw
    exact hdiff w hw

theorem RestModel.homology_of_torus' (R : RestModel M Q Z n V₁ V₂) (hn : 2 ≤ n)
    (h31 : ∀ v ∈ Q, v ≠ 1 → (InZClass Z v ↔ v ∈ V₁ ∨ v ∈ V₂)) {Y : Subgroup G}
    (hY : Ctx M Q Z Y) (hYV : Y ≤ V₂) (hmod : V₂ ≤ QB Y) {x : G} (hxX : x ∈ Q ⊔ QB Y)
    (hxZ : x ∈ Subgroup.normalizer (Z : Set G)) (hxY : x ∈ Subgroup.normalizer (Y : Set G)) :
    ∃ (ν : R.Kˣ) (f : R.M₀.E →ₗ[R.K] R.M₀.E) (b : R.M₀.E),
      IsHomology R.M₀ M R.W₂ x ν f b ∧ (∀ w ∈ R.W₁, f w ∈ R.W₁) ∧ (∀ w ∈ R.W₂, f w ∈ R.W₂) := by
  classical
  have H := R.hyp
  obtain ⟨ν, f, b, hh⟩ := R.homology_of_torus hn hY hYV hmod hxX hxZ hxY
  have hbW : b ∈ R.W₂ := hh.b_mem
  have hW₂ : ∀ w ∈ R.W₂, f w ∈ R.W₂ := fun w hw => by
    have h1 : f w = w + (f w - w) := by abel
    rw [h1]
    exact R.W₂.add_mem hw ((Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hbW))
      (hh.hom w hw))
  have hV₂n : ∀ v ∈ V₂, x * v * x⁻¹ ∈ V₂ := fun v hv => by
    have hvQ := R.V₂Q hv
    have h1 := hW₂ (R.M₀.π v) ((R.memW₂ _).mpr (R.M₀.pi_mem_img hv hvQ))
    rw [← hh.act v hvQ] at h1
    exact (R.M₀.mem_img_iff R.ZV₂ (conj_mem_Q H hh.mem hvQ)).mp ((R.memW₂ _).mp h1)
  have hV₂N : x ∈ Subgroup.normalizer (V₂ : Set G) := by
    refine conjSubgroup_eq_self_iff.mp (Subgroup.eq_of_le_of_card_ge ?_ (by
      rw [card_conjSubgroup]))
    intro y hy
    rw [mem_conjSubgroup] at hy
    have h1 := hV₂n _ hy
    have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rw [e] at h1
    exact h1
  have hV₁n : ∀ v ∈ V₁, x * v * x⁻¹ ∈ V₁ := by
    intro v hv
    by_cases hv1 : v = 1
    · subst hv1; simp [V₁.one_mem]
    have hvQ : v ∈ Q := R.V₁Q hv
    have hcl : InZClass Z v := (h31 v hvQ hv1).mpr (Or.inl hv)
    obtain ⟨g, z, hz, hz1, hvg⟩ := hcl
    have hxvQ : x * v * x⁻¹ ∈ Q := conj_mem_Q H hh.mem hvQ
    have hxv1 : x * v * x⁻¹ ≠ 1 := by
      intro h; apply hv1
      have : v = x⁻¹ * (x * v * x⁻¹) * x := by group
      rw [this, h]; group
    have hcl' : InZClass Z (x * v * x⁻¹) := ⟨x * g, z, hz, hz1, by rw [hvg]; group⟩
    rcases (h31 _ hxvQ hxv1).mp hcl' with h | h
    · exact h
    · have hvV₂ : v ∈ V₂ := by
        have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hV₂N) _).mp h
        have e : x⁻¹ * (x * v * x⁻¹) * x⁻¹⁻¹ = v := by group
        rw [e] at h2
        exact h2
      have hvZ : v ∈ Z := by rw [← R.V₁₂]; exact ⟨hv, hvV₂⟩
      exact R.ZV₁ ((Subgroup.mem_normalizer_iff.mp hxZ v).mp hvZ)
  refine ⟨ν, f, b, hh, fun w hw => ?_, hW₂⟩
  obtain ⟨v, hvV, hvQ, rfl⟩ := (R.memW₁ w).mp hw
  rw [← hh.act v hvQ]
  exact (R.memW₁ _).mpr (R.M₀.pi_mem_img (hV₁n v hvV) (conj_mem_Q H hh.mem hvQ))

theorem RestModel.mult_pow (R : RestModel M Q Z n V₁ V₂) {x : G}
    (hxZ : x ∈ Subgroup.normalizer (Z : Set G)) {ν : R.K}
    (hmult : ∀ z ∈ Z, R.γ (x * z * x⁻¹) = ν * R.γ z) (i : ℕ) :
    ∀ z ∈ Z, x ^ i * z * (x ^ i)⁻¹ ∈ Z ∧
      R.γ (x ^ i * z * (x ^ i)⁻¹) = ν ^ i * R.γ z := by
  induction i with
  | zero => intro z hz; simpa using hz
  | succ i ih =>
    intro z hz
    obtain ⟨h1, h2⟩ := ih z hz
    have e : x ^ (i + 1) * z * (x ^ (i + 1))⁻¹ = x * (x ^ i * z * (x ^ i)⁻¹) * x⁻¹ := by
      group
    rw [e]
    refine ⟨(Subgroup.mem_normalizer_iff.mp hxZ _).mp h1, ?_⟩
    rw [hmult _ h1, h2, pow_succ]
    ring

theorem RestModel.cartan_homology (R : RestModel M Q Z n V₁ V₂) (hn : 2 ≤ n)
    (h31 : ∀ v ∈ Q, v ≠ 1 → (InZClass Z v ↔ v ∈ V₁ ∨ v ∈ V₂)) {Y : Subgroup G}
    (hY : Ctx M Q Z Y) (hYV : Y ≤ V₂) (hmod : V₂ ≤ QB Y) (ν₀ : R.Kˣ)
    (hν₀ : orderOf ν₀ = Nat.card Z - 1) :
    ∃ (k : G) (f : R.M₀.E →ₗ[R.K] R.M₀.E) (b : R.M₀.E),
      IsHomology R.M₀ M R.W₂ k ν₀ f b ∧ (∀ w ∈ R.W₁, f w ∈ R.W₁) ∧ (∀ w ∈ R.W₂, f w ∈ R.W₂) := by
  classical
  have H := R.hyp
  obtain ⟨x, hxX, hxZ, hxY, hreg⟩ := Ctx.exists_torus hY
  obtain ⟨ν, f, b, hh, -, -⟩ := R.homology_of_torus' hn h31 hY hYV hmod hxX hxZ hxY
  have hZne : ∃ z ∈ Z, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card Z = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩, ⟨1⟩⟩
    have := H.q4
    omega
  obtain ⟨z₀, hz₀, hz₀1⟩ := hZne
  have hγz₀ : R.γ z₀ ≠ 0 := fun h => hz₀1 (R.gm.reg.inj z₀ hz₀ h)
  have hνne : ∀ i : ℕ, 0 < i → i < Nat.card Z - 1 → ν ^ i ≠ 1 := by
    intro i hi0 hi h1
    apply hz₀1
    have h2 : (ν : R.K) ^ i = 1 := by
      have := congrArg Units.val h1
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
    obtain ⟨hzi, hγi⟩ := R.mult_pow hxZ hh.mult i z₀ hz₀
    rw [h2, one_mul] at hγi
    have h3 : x ^ i * z₀ * (x ^ i)⁻¹ = z₀ := R.gm.reg.eq_of_γ_eq hzi hz₀ hγi
    exact hreg i hi0 hi z₀ hz₀ (by
      calc x ^ i * z₀ = (x ^ i * z₀ * (x ^ i)⁻¹) * x ^ i := by group
        _ = z₀ * x ^ i := by rw [h3])
  have hcardU : Nat.card R.Kˣ = Nat.card Z - 1 := by
    rw [Nat.card_units, R.gm.card]
  have hord : orderOf ν = Nat.card Z - 1 := by
    have hle : orderOf ν ≤ Nat.card Z - 1 := by
      rw [← hcardU]; exact Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard ν)
    by_contra hne
    have hlt : orderOf ν < Nat.card Z - 1 := lt_of_le_of_ne hle hne
    exact hνne (orderOf ν) (orderOf_pos ν) hlt (pow_orderOf_eq_one ν)
  have htop : Subgroup.zpowers ν = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hcardU]
  have hmem : ν₀ ∈ Submonoid.powers ν := by
    rw [mem_powers_iff_mem_zpowers, htop]; exact Subgroup.mem_top _
  obtain ⟨j, hj⟩ := hmem
  have hxjX : x ^ j ∈ Q ⊔ QB Y := Subgroup.pow_mem _ hxX j
  have hxjZ : x ^ j ∈ Subgroup.normalizer (Z : Set G) := Subgroup.pow_mem _ hxZ j
  have hxjY : x ^ j ∈ Subgroup.normalizer (Y : Set G) := Subgroup.pow_mem _ hxY j
  obtain ⟨ν', f', b', hh', hf₁, hf₂⟩ := R.homology_of_torus' hn h31 hY hYV hmod hxjX hxjZ hxjY
  have hνν : ν' = ν₀ := by
    obtain ⟨-, hγj⟩ := R.mult_pow hxZ hh.mult j z₀ hz₀
    have h1 := hh'.mult z₀ hz₀
    rw [h1] at hγj
    have h2 : (ν' : R.K) = (ν : R.K) ^ j := mul_right_cancel₀ hγz₀ hγj
    apply Units.ext
    rw [h2, ← hj, Units.val_pow_eq_pow_val]
  subst hνν
  exact ⟨x ^ j, f', b', hh', hf₁, hf₂⟩

end Homology

end CFSG.RankThree.GF2n.Smith81
