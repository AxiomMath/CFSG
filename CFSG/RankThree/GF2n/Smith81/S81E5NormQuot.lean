module

public import CFSG.RankThree.GF2n.Smith81.S81E5FormHolds
public import CFSG.RankThree.GF2n.Smith81.S81UAct
public import CFSG.RankThree.GF2n.Smith81.S81TCond
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutMain
public import TauCeti.Algebra.Group.Coprime

public section


namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.ModelFacts.ChevAut

variable {K : Type} [Field K]

theorem mul_xu_of_mul_xu_one {T : (Module.End K (V K))ˣ} {γ : Fin (Tag.rank .E7) → ℤ} {b : K}
    (h : T * e7Data_valid.xu K γ 1 = e7Data_valid.xu K γ b * T) (c : K) :
    T * e7Data_valid.xu K γ c = e7Data_valid.xu K γ (b * c) * T := by
  have h1 := congrArg Units.val h
  rw [Units.val_mul, Units.val_mul, e7Data_valid.xu_val, e7Data_valid.xu_val, one_smul, mul_add,
    add_mul, mul_one, one_mul, add_right_inj, smul_mul_assoc] at h1
  ext1
  rw [Units.val_mul, Units.val_mul, e7Data_valid.xu_val, e7Data_valid.xu_val, mul_add, add_mul,
    mul_one, one_mul, mul_smul_comm, h1, smul_smul, smul_mul_assoc, mul_comm c b]

theorem pow_mul_xu {T : (Module.End K (V K))ˣ} {γ : Fin (Tag.rank .E7) → ℤ} {b : K}
    (h : ∀ c, T * e7Data_valid.xu K γ c = e7Data_valid.xu K γ (b * c) * T) (n : ℕ) (c : K) :
    T ^ n * e7Data_valid.xu K γ c = e7Data_valid.xu K γ (b ^ n * c) * T ^ n := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [pow_succ T n, pow_succ b n, mul_assoc (T ^ n) T, h c, ← mul_assoc (T ^ n), ih (b * c),
      mul_assoc _ (T ^ n) T, mul_assoc (b ^ n) b c]

theorem eq_top_of_xm_single_mem {S : Subgroup (EGrp K)}
    (h : ∀ i c, e7Data_valid.xm K (Pi.single i 1) c ∈ S ∧
      e7Data_valid.xm K (-Pi.single i 1) c ∈ S) : S = ⊤ := by
  rw [eq_top_iff, ← iSup_leviAmalgam_eq_top (isCTRootSystem (e7Datum K).isFiniteType
    (e7Datum K).divisible) (e7Datum_isCTGroupDatum K)]
  refine iSup_le fun J => iSup₂_le fun j _ => sup_le ?_ ?_
  · intro y hy
    obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hy
    exact (h j c).1
  · intro y hy
    obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hy
    exact (h j c).2

theorem pow_card_sub_one_mul_self_eq_one [Fintype K] [CharP K 2] {T : (Module.End K (V K))ˣ}
    (h : ∀ i : Fin (Tag.rank .E7),
      (∃ b : Kˣ, T * e7Data_valid.xu K (Pi.single i 1) 1 =
        e7Data_valid.xu K (Pi.single i 1) b * T) ∧
      ∃ b : Kˣ, T * e7Data_valid.xu K (-Pi.single i 1) 1 =
        e7Data_valid.xu K (-Pi.single i 1) b * T) :
    T ^ ((Fintype.card K - 1) * (Fintype.card K - 1)) = 1 := by
  obtain ⟨N, hN⟩ : ∃ N, N = Fintype.card K - 1 := ⟨_, rfl⟩
  rw [← hN]
  have hbN : ∀ b : Kˣ, (b : K) ^ N = 1 := fun b => by
    rw [hN]
    exact FiniteField.pow_card_sub_one_eq_one _ b.ne_zero
  have hroot : ∀ {γ : Fin (Tag.rank .E7) → ℤ} (b : Kˣ),
      T * e7Data_valid.xu K γ 1 = e7Data_valid.xu K γ b * T →
        ∀ c, T ^ N * e7Data_valid.xu K γ c = e7Data_valid.xu K γ c * T ^ N := by
    intro γ b hb c
    rw [pow_mul_xu (mul_xu_of_mul_xu_one hb) N c, hbN, one_mul]
  have hcen : ∀ y ∈ EGrp K, T ^ N * y = y * T ^ N := by
    have htop := eq_top_of_xm_single_mem
      (S := (Subgroup.centralizer {T ^ N}).comap (EGrp K).subtype) fun i c => by
        obtain ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩ := h i
        exact ⟨Subgroup.mem_comap.mpr
            (Subgroup.mem_centralizer_singleton_iff.mpr (hroot b hb c).symm),
          Subgroup.mem_comap.mpr
            (Subgroup.mem_centralizer_singleton_iff.mpr (hroot b' hb' c).symm)⟩
    intro y hy
    have hmem : (⟨y, hy⟩ : EGrp K) ∈ (Subgroup.centralizer {T ^ N}).comap (EGrp K).subtype := by
      rw [htop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp hmem)).symm
  obtain ⟨μ, hμ⟩ := schur_V (K := K)
    (T := ((T ^ N : (Module.End K (V K))ˣ) : Module.End K (V K))) fun g hg v => by
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hg
      exact congrArg (fun w : (Module.End K (V K))ˣ => (w : Module.End K (V K)) v) (hcen u hu)
  have hpow : ∀ n : ℕ, ∀ v : V K,
      (((T ^ N) ^ n : (Module.End K (V K))ˣ) : Module.End K (V K)) v = μ ^ n • v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ (T ^ N) n, Units.val_mul, Module.End.mul_apply, hμ, map_smul, ih, smul_smul,
        ← pow_succ']
  have hq : (T ^ N) ^ (N + 1) = T ^ N := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    rw [hpow, hμ, hN, Nat.sub_add_cancel Fintype.card_pos, FiniteField.pow_card]
  rw [pow_succ] at hq
  rw [pow_mul]
  exact mul_right_cancel (b := T ^ N) (by rw [one_mul]; exact hq)

section Normalizer


theorem mem_EGrp_of_normalizes [Finite K] [CharP K 2] {T : (Module.End K (V K))ˣ}
    (hT : ∀ g ∈ EGrp K, T * g * T⁻¹ ∈ EGrp K) {k : ℕ} (hk : T ^ (2 ^ k) = 1) : T ∈ EGrp K := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hTn : ∀ n : ℕ, ∀ y ∈ EGrp K, T ^ n * y * (T ^ n)⁻¹ ∈ EGrp K := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      have e : T ^ (n + 1) * y * (T ^ (n + 1))⁻¹ = T * (T ^ n * y * (T ^ n)⁻¹) * T⁻¹ := by
        rw [pow_succ']
        group
      rw [e]
      exact hT _ (ih y hy)
  have hinv : T ^ (2 ^ k - 1) = T⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, hk]
  have hTinv : ∀ y ∈ EGrp K, T⁻¹ * y * T ∈ EGrp K := by
    intro y hy
    have h := hTn (2 ^ k - 1) y hy
    rwa [hinv, inv_inv] at h
  have hN : T ∈ Subgroup.normalizer (EGrp K : Set (Module.End K (V K))ˣ) :=
    Subgroup.mem_normalizer_iff.mpr fun y =>
      ⟨hT y, fun hy => by
        have h := hTinv _ hy
        rwa [show T⁻¹ * (T * y * T⁻¹) * T = y by group] at h⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : EGrp K ≃* EGrp K, ∀ y : EGrp K,
      ((σ y : EGrp K) : (Module.End K (V K))ˣ) = T * y * T⁻¹ :=
    ⟨{ toFun := fun y => ⟨T * y * T⁻¹, hT y y.2⟩
       invFun := fun y => ⟨T⁻¹ * y * T, hTinv y y.2⟩
       left_inv := fun y => Subtype.ext (by simp only; group)
       right_inv := fun y => Subtype.ext (by simp only; group)
       map_mul' := fun y z => Subtype.ext (by simp only [Subgroup.coe_mul]; group) },
      fun y => rfl⟩
  obtain ⟨α, g, a, φ, ε, hα, hroot⟩ := excAut_E7 (F := K) (p := 2) (MonoidHom.id (EGrp K))
    Function.surjective_id (by rw [MonoidHom.ker_id]; exact bot_le) σ
  have hT₁ : ∀ (γ : Fin (Tag.rank .E7) → ℤ) (b : Kˣ),
      α (e7Data_valid.xm K γ 1) = g * e7Data_valid.xm K γ b * g⁻¹ →
        (g : (Module.End K (V K))ˣ)⁻¹ * T * e7Data_valid.xu K γ 1 =
          e7Data_valid.xu K γ b * ((g : (Module.End K (V K))ˣ)⁻¹ * T) := by
    intro γ b h
    have h1 : T * e7Data_valid.xu K γ 1 * T⁻¹ =
        (g : (Module.End K (V K))ˣ) * e7Data_valid.xu K γ b * (g : (Module.End K (V K))ˣ)⁻¹ := by
      have h' := congrArg Subtype.val ((hα (e7Data_valid.xm K γ 1)).symm.trans h)
      rw [hσ] at h'
      exact h'
    calc (g : (Module.End K (V K))ˣ)⁻¹ * T * e7Data_valid.xu K γ 1
        = (g : (Module.End K (V K))ˣ)⁻¹ * (T * e7Data_valid.xu K γ 1 * T⁻¹) * T := by group
      _ = (g : (Module.End K (V K))ˣ)⁻¹ * ((g : (Module.End K (V K))ˣ) * e7Data_valid.xu K γ b *
            (g : (Module.End K (V K))ˣ)⁻¹) * T := by rw [h1]
      _ = e7Data_valid.xu K γ b * ((g : (Module.End K (V K))ˣ)⁻¹ * T) := by group
  have hπ : ∀ i, CFSG.LieType.Chevalley.exactPerm Tag.E7 ε i = i := fun i => rfl
  have hfin := pow_card_sub_one_mul_self_eq_one (T := (g : (Module.End K (V K))ˣ)⁻¹ * T)
    fun i => by
      have h1 := (hroot i 1).1
      have h2 := (hroot i 1).2
      simp only [hπ, map_one, mul_one] at h1 h2
      exact ⟨⟨a i, hT₁ _ _ h1⟩, ⟨(a i)⁻¹, hT₁ _ _ h2⟩⟩
  have hT₁N : (g : (Module.End K (V K))ˣ)⁻¹ * T ∈
      Subgroup.normalizer (EGrp K : Set (Module.End K (V K))ˣ) :=
    mul_mem (inv_mem (Subgroup.le_normalizer g.2)) hN
  have hrel : ∀ n : ℕ, T ^ n * (((g : (Module.End K (V K))ˣ)⁻¹ * T) ^ n)⁻¹ ∈ EGrp K := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc := (Subgroup.mem_normalizer_iff.mp (pow_mem hT₁N n) g).mp g.2
      have e : ∀ P : (Module.End K (V K))ˣ,
          T ^ n * T * (P * ((g : (Module.End K (V K))ˣ)⁻¹ * T))⁻¹ = T ^ n * P⁻¹ * (P * g * P⁻¹) :=
        fun P => by group
      rw [pow_succ T n, pow_succ ((g : (Module.End K (V K))ˣ)⁻¹ * T) n, e]
      exact mul_mem ih hc
  have hpowmem : T ^ ((Fintype.card K - 1) * (Fintype.card K - 1)) ∈ EGrp K := by
    have h := hrel ((Fintype.card K - 1) * (Fintype.card K - 1))
    rwa [hfin, inv_one, mul_one] at h
  have hodd : ¬ 2 ∣ Fintype.card K - 1 := by
    have h2 : 2 ∣ Fintype.card K :=
      (CharP.cast_eq_zero_iff K 2 _).mp (FiniteField.cast_card_eq_zero K)
    have hpos : 0 < Fintype.card K := Fintype.card_pos
    omega
  have hcop : Nat.Coprime ((Fintype.card K - 1) * (Fintype.card K - 1)) (2 ^ k) := by
    have h2 : Nat.Coprime (Fintype.card K - 1) 2 :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).symm
    exact Nat.Coprime.pow_right k (Nat.Coprime.mul_left h2 h2)
  obtain ⟨i, j, hij⟩ := TauCeti.exists_zpow_mul_zpow_eq_of_coprime
    (G := (Module.End K (V K))ˣ) hcop
  rw [← hij T, hk, one_zpow, mul_one]
  exact zpow_mem hpowmem i

theorem mem_EAut_of_normalizes [Finite K] [CharP K 2] {T : V K ≃ₗ[K] V K}
    (hT : ∀ g ∈ EAut K, ∃ g' ∈ EAut K, T * g = g' * T) {k : ℕ} (hk : T ^ (2 ^ k) = 1) :
    T ∈ EAut K := by
  rw [mem_EAut_iff]
  refine mem_EGrp_of_normalizes (fun g hg => ?_) (k := k) (by rw [← map_pow, hk, map_one])
  obtain ⟨g', hg', h⟩ := hT (vAut K g)
    (mem_EAut_iff.mpr (by rw [MulEquiv.symm_apply_apply]; exact hg))
  have h2 : T * vAut K g * T⁻¹ = g' := by rw [h, mul_inv_cancel_right]
  have h3 : (vAut K).symm T * g * ((vAut K).symm T)⁻¹ = (vAut K).symm g' := by
    rw [← h2, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rw [h3]
  exact mem_EAut_iff.mp hg'

end Normalizer

end CFSG.RankThree.GF2n.Smith81.E7Model

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.GF2n.Smith81.E7Model


theorem normQuotE5_of_uniform (hFE1 : Smith24E5UniformStatement) :
    NormQuotE5Statement := by
  intro G _ _ M Q Z B IH hc h5 E hEH0 hE2
  obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hc.ctx.hyp
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h5 K γ M₀ hg
  have hctx : Ctx M Q Z B := hc.ctx
  have hEL : E ≤ Lgen M (LB M Q B) := by
    intro m hm
    have hmM : m ∈ M := (Subgroup.mem_inf.mp (hEH0 hm)).1
    obtain ⟨T, hT⟩ := exists_actsOnQtAsU hg ψ (hEH0 hm)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hE2) ⟨m, hm⟩
    have hmk : m ^ (2 ^ k) = 1 := by
      have h1 := pow_orderOf_eq_one (⟨m, hm⟩ : E)
      rw [hk] at h1
      exact congrArg Subtype.val h1
    exact hT.mem_Lgen hctx d hmM (mem_EAut_of_normalizes (hT.normalizesGamma hctx d hmM)
      (hT.pow_eq_one hctx.hyp hmM hmk))
  rw [inf_eq_left.mpr hEL]
  omega

end CFSG.RankThree.GF2n.Smith81
