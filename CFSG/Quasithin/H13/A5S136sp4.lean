module

public import CFSG.Quasithin.H13.A5S136sp3
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Std

public section

namespace CFSG.Quasithin.H13.A5.SpBorel

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauAut tauAut_proj tauMat_apply
  tauPair_ι₀ tauPair_ι₁ tauPair_ι₂ tauPair_ι₃)

variable {K : Type} [Field K] [Finite K]

theorem exists_pow_eq_of_charTwo [CharP K 2] (ρ : K ≃+* K) : ∃ m : ℕ, ∀ c, ρ c = c ^ 2 ^ m := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨φ, hφ, hord, hzp, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two n.pos hK
  have hfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; exact n.pos)
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp
    (hfin.mem_powers_iff_mem_zpowers.mpr (hzp ▸ Subgroup.mem_top ρ))
  have hpow : ∀ (j : ℕ) (c : K), (φ ^ j) c = c ^ 2 ^ j := by
    intro j
    induction j with
    | zero => intro c; simp
    | succ j ih =>
      intro c
      rw [pow_succ]
      show (φ ^ j) (φ c) = _
      rw [ih, hφ, ← pow_mul, ← pow_succ']
  exact ⟨m, fun c => by rw [← hm, hpow]⟩

omit [Finite K] in
theorem diagHom_torusHom (s : Fin 2 → Kˣ) :
    diagHom 2 K ⟨SymplecticTorusWeyl.torusHom s, torus_le_borelSubgroup ⟨s, rfl⟩⟩ = s := by
  funext i
  apply Units.ext
  simp [diagHom, diagEntry, SymplecticTorusWeyl.coe_torusHom]

omit [Finite K] in
theorem diagHom_eq_one_iff (b : borelSubgroup 2 K) :
    diagHom 2 K b = 1 ↔ (b : StatedSp 2 K) ∈ unipotent 2 K := by
  rw [← MonoidHom.mem_ker, ker_diagHom, Subgroup.mem_subgroupOf]

@[expose] def tauT (s : Fin 2 → Kˣ) : Fin 2 → Kˣ := ![s 0 * s 1, s 0 * (s 1)⁻¹]

omit [Finite K] in
theorem tauSp_torusHom [CharP K 2] (s : Fin 2 → Kˣ) :
    tauSp (SymplecticTorusWeyl.torusHom s) = SymplecticTorusWeyl.torusHom (tauT s) := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_tauSp, SymplecticTorusWeyl.coe_torusHom, SymplecticTorusWeyl.coe_torusHom]
  ext r c
  rcases r with r | r <;> rcases c with c | c <;> fin_cases r <;> fin_cases c <;>
    simp [tauMat_apply, CFSG.QuasithinUnique.Lin2.Five.tauPair, tauT, mul_comm]

omit [Finite K] in
theorem fieldSp_torusHom (σ : K ≃+* K) (s : Fin 2 → Kˣ) :
    fieldSp 2 K σ (SymplecticTorusWeyl.torusHom s) =
      SymplecticTorusWeyl.torusHom (fun i => Units.map (σ : K →* K) (s i)) := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_fieldSp, SymplecticTorusWeyl.coe_torusHom, SymplecticTorusWeyl.coe_torusHom]
  ext r c
  rcases r with r | r <;> rcases c with c | c <;>
    by_cases hrc : r = c <;> simp [hrc]

omit [Finite K] in
theorem tauSp_mem_borel [CharP K 2] {b : StatedSp 2 K} (hb : b ∈ borelSubgroup 2 K) :
    tauSp b ∈ borelSubgroup 2 K := by
  obtain ⟨u, hu, s, rfl⟩ := Sp4.borelSubgroup_decomp hb
  rw [map_mul, tauSp_torusHom]
  exact (borelSubgroup 2 K).mul_mem (unipotent_le_borelSubgroup (Sp4.tauSp_mem_unipotent hu))
    (torus_le_borelSubgroup ⟨_, rfl⟩)

omit [Finite K] in
theorem fieldSp_mem_borel [CharP K 2] (σ : K ≃+* K) {b : StatedSp 2 K}
    (hb : b ∈ borelSubgroup 2 K) : fieldSp 2 K σ b ∈ borelSubgroup 2 K := by
  obtain ⟨u, hu, s, rfl⟩ := Sp4.borelSubgroup_decomp hb
  rw [map_mul, fieldSp_torusHom]
  exact (borelSubgroup 2 K).mul_mem
    (unipotent_le_borelSubgroup (Sp4.fieldSp_mem_unipotent σ hu)) (torus_le_borelSubgroup ⟨_, rfl⟩)

omit [Finite K] in
theorem diagHom_tauSp [CharP K 2] {b : StatedSp 2 K} (hb : b ∈ borelSubgroup 2 K) :
    diagHom 2 K ⟨tauSp b, tauSp_mem_borel hb⟩ = tauT (diagHom 2 K ⟨b, hb⟩) := by
  obtain ⟨u, hu, s, rfl⟩ := Sp4.borelSubgroup_decomp hb
  have hu' : tauSp u ∈ borelSubgroup 2 K :=
    unipotent_le_borelSubgroup (Sp4.tauSp_mem_unipotent hu)
  have h1 : (⟨tauSp (u * SymplecticTorusWeyl.torusHom s), tauSp_mem_borel hb⟩ :
      borelSubgroup 2 K) = ⟨tauSp u, hu'⟩ *
        ⟨SymplecticTorusWeyl.torusHom (tauT s), torus_le_borelSubgroup ⟨_, rfl⟩⟩ :=
    Subtype.ext (by
      show tauSp (u * SymplecticTorusWeyl.torusHom s) =
        tauSp u * SymplecticTorusWeyl.torusHom (tauT s)
      rw [map_mul, tauSp_torusHom])
  have h2 : (⟨u * SymplecticTorusWeyl.torusHom s, hb⟩ : borelSubgroup 2 K) =
      ⟨u, unipotent_le_borelSubgroup hu⟩ *
        ⟨SymplecticTorusWeyl.torusHom s, torus_le_borelSubgroup ⟨_, rfl⟩⟩ := rfl
  rw [h1, h2, map_mul, map_mul, diagHom_torusHom, diagHom_torusHom,
    (diagHom_eq_one_iff _).mpr (Sp4.tauSp_mem_unipotent hu), (diagHom_eq_one_iff _).mpr hu,
    one_mul, one_mul]

omit [Finite K] in
theorem diagHom_fieldSp [CharP K 2] (σ : K ≃+* K) {b : StatedSp 2 K}
    (hb : b ∈ borelSubgroup 2 K) :
    diagHom 2 K ⟨fieldSp 2 K σ b, fieldSp_mem_borel σ hb⟩ =
      fun i => Units.map (σ : K →* K) (diagHom 2 K ⟨b, hb⟩ i) := by
  obtain ⟨u, hu, s, rfl⟩ := Sp4.borelSubgroup_decomp hb
  have hu' : fieldSp 2 K σ u ∈ borelSubgroup 2 K :=
    unipotent_le_borelSubgroup (Sp4.fieldSp_mem_unipotent σ hu)
  have h1 : (⟨fieldSp 2 K σ (u * SymplecticTorusWeyl.torusHom s), fieldSp_mem_borel σ hb⟩ :
      borelSubgroup 2 K) = ⟨fieldSp 2 K σ u, hu'⟩ *
        ⟨SymplecticTorusWeyl.torusHom (fun i => Units.map (σ : K →* K) (s i)),
          torus_le_borelSubgroup ⟨_, rfl⟩⟩ :=
    Subtype.ext (by
      show fieldSp 2 K σ (u * SymplecticTorusWeyl.torusHom s) = fieldSp 2 K σ u *
        SymplecticTorusWeyl.torusHom (fun i => Units.map (σ : K →* K) (s i))
      rw [map_mul, fieldSp_torusHom])
  have h2 : (⟨u * SymplecticTorusWeyl.torusHom s, hb⟩ : borelSubgroup 2 K) =
      ⟨u, unipotent_le_borelSubgroup hu⟩ *
        ⟨SymplecticTorusWeyl.torusHom s, torus_le_borelSubgroup ⟨_, rfl⟩⟩ := rfl
  rw [h1, h2, map_mul, map_mul, diagHom_torusHom, diagHom_torusHom,
    (diagHom_eq_one_iff _).mpr (Sp4.fieldSp_mem_unipotent σ hu), (diagHom_eq_one_iff _).mpr hu,
    one_mul, one_mul]

theorem pow_eq_pow_mod_three {G : Type*} [Monoid G] {x : G} (hx : x ^ 3 = 1) (n : ℕ) :
    x ^ n = x ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one]

theorem eq_one_of_cube_sq {G : Type*} [Group G] {x : G} (h3 : x ^ 3 = 1) (h2 : x ^ 2 = 1) :
    x = 1 := by
  calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; group

theorem two_pow_mod_three (m : ℕ) : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
  have h : ¬ 3 ∣ 2 ^ m := fun h3 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  omega

omit [Finite K] in
theorem arith5 {m : ℕ} (ε : Bool) {a b : Fin 2 → Kˣ} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (ha : (fun i => ((if ε then tauT a else a) i) ^ 2 ^ m) * a = 1) (hb3 : b ^ 3 = 1) :
    (fun i => ((if ε then tauT b else b) i) ^ 2 ^ m) * b = 1 := by
  have ha3' : ∀ i, a i ^ 3 = 1 := fun i => by simpa using congrFun ha3 i
  have hb3' : ∀ i, b i ^ 3 = 1 := fun i => by simpa using congrFun hb3 i
  have ha' : ∀ i, ((if ε then tauT a else a) i) ^ 2 ^ m * a i = 1 :=
    fun i => by simpa using congrFun ha i
  have hne : ¬ (a 0 = 1 ∧ a 1 = 1) := fun h => ha1 (funext fun i => by
    fin_cases i
    · exact h.1
    · exact h.2)
  cases ε
  ·
    simp only [Bool.false_eq_true, ↓reduceIte] at ha' ⊢
    rcases two_pow_mod_three m with hr | hr
    · exfalso
      apply hne
      refine ⟨eq_one_of_cube_sq (ha3' 0) ?_, eq_one_of_cube_sq (ha3' 1) ?_⟩
      · have := ha' 0
        rwa [pow_eq_pow_mod_three (ha3' 0), hr, pow_one, ← pow_two] at this
      · have := ha' 1
        rwa [pow_eq_pow_mod_three (ha3' 1), hr, pow_one, ← pow_two] at this
    · funext i
      show b i ^ 2 ^ m * b i = 1
      rw [pow_eq_pow_mod_three (hb3' i), hr, ← pow_succ, hb3' i]
  ·
    exfalso
    simp only [↓reduceIte, tauT] at ha'
    have h0 := ha' 0
    have h1 := ha' 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have hab3 : (a 0 * a 1) ^ 3 = 1 := by rw [mul_pow, ha3' 0, ha3' 1, one_mul]
    have hab3' : (a 0 * (a 1)⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, ha3' 0, ha3' 1, inv_one,
      one_mul]
    rw [pow_eq_pow_mod_three hab3] at h0
    rw [pow_eq_pow_mod_three hab3'] at h1
    apply hne
    rcases two_pow_mod_three m with hr | hr <;> rw [hr] at h0 h1
    ·
      have e0 : a 0 = 1 := by simpa using h1
      refine ⟨e0, ?_⟩
      simpa [e0] using h0
    ·
      have e1 : a 1 = 1 := by
        refine eq_one_of_cube_sq (ha3' 1) ?_
        have e : (a 0 * a 1) ^ 2 * a 0 = a 0 ^ 3 * a 1 ^ 2 := by
          rw [mul_pow, mul_right_comm, ← pow_succ]
        rw [e, ha3' 0, one_mul] at h0
        exact h0
      refine ⟨eq_one_of_cube_sq (ha3' 0) ?_, e1⟩
      simpa [e1] using h1

theorem proj_mem_projUnipotent_iff {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (x : StatedSp 2 K) : proj 2 K x ∈ projUnipotent 2 K ↔ x ∈ unipotent 2 K := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [← proj_injective (f := n) hn (by norm_num) hK hxy]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem model5 [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {α : MulAut (StatedProj (StatedSp 2 K))}
    (hα : ∀ x, α x ∈ projUnipotent 2 K ↔ x ∈ projUnipotent 2 K)
    {k : StatedProj (StatedSp 2 K)}
    (hkN : k ∈ Subgroup.normalizer (projUnipotent 2 K : Set (StatedProj (StatedSp 2 K))))
    (hk3 : orderOf k = 3) (hkinv : α k * k ∈ projUnipotent 2 K)
    {h : StatedProj (StatedSp 2 K)}
    (hhN : h ∈ Subgroup.normalizer (projUnipotent 2 K : Set (StatedProj (StatedSp 2 K))))
    (hh3 : h ^ 3 = 1) : α h * h ∈ projUnipotent 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ, u, s, ε, hu, rfl⟩ := Sp4.exists_standard_form hn hK hα
  obtain ⟨m, hm⟩ := exists_pow_eq_of_charTwo σ
  have hinj := proj_injective (f := n) (r := 2) hn (by norm_num) hK
  set g := u * SymplecticTorusWeyl.torusHom s with hg
  set α₀ : MulAut (StatedProj (StatedSp 2 K)) :=
    MulAut.conj (proj 2 K g) * fieldAut 2 K σ * (if ε then tauAut else 1) with hα₀
  have hgB : g ∈ borelSubgroup 2 K :=
    (borelSubgroup 2 K).mul_mem (unipotent_le_borelSubgroup hu) (torus_le_borelSubgroup ⟨s, rfl⟩)
  set τε : StatedSp 2 K →* StatedSp 2 K := if ε then tauSp else MonoidHom.id _ with hτε
  have hτεB : ∀ {b}, b ∈ borelSubgroup 2 K → τε b ∈ borelSubgroup 2 K := by
    intro b hb
    cases ε
    · exact hb
    · exact tauSp_mem_borel hb
  have happly : ∀ b : StatedSp 2 K,
      α₀ (proj 2 K b) = proj 2 K (g * fieldSp 2 K σ (τε b) * g⁻¹) := by
    intro b
    have h1 : (if ε then tauAut else 1) (proj 2 K b) = proj 2 K (τε b) := by
      cases ε
      · rfl
      · exact tauAut_proj b
    rw [hα₀, MulAut.mul_apply, MulAut.mul_apply, h1, fieldAut_proj, MulAut.conj_apply, ← map_inv,
      ← map_mul, ← map_mul]
  have hcrit : ∀ b (hb : b ∈ borelSubgroup 2 K),
      α₀ (proj 2 K b) * proj 2 K b ∈ projUnipotent 2 K ↔
      (fun i => ((if ε then tauT (diagHom 2 K ⟨b, hb⟩) else diagHom 2 K ⟨b, hb⟩) i) ^ 2 ^ m) *
        diagHom 2 K ⟨b, hb⟩ = 1 := by
    intro b hb
    have hfB := fieldSp_mem_borel σ (hτεB hb)
    have hwB : g * fieldSp 2 K σ (τε b) * g⁻¹ * b ∈ borelSubgroup 2 K :=
      (borelSubgroup 2 K).mul_mem ((borelSubgroup 2 K).mul_mem
        ((borelSubgroup 2 K).mul_mem hgB hfB) ((borelSubgroup 2 K).inv_mem hgB)) hb
    rw [happly, ← map_mul, proj_mem_projUnipotent_iff hn hK,
      ← diagHom_eq_one_iff (⟨_, hwB⟩ : borelSubgroup 2 K)]
    have hw : (⟨g * fieldSp 2 K σ (τε b) * g⁻¹ * b, hwB⟩ : borelSubgroup 2 K) =
        ⟨g, hgB⟩ * ⟨_, hfB⟩ * (⟨g, hgB⟩)⁻¹ * ⟨b, hb⟩ := rfl
    have hD : diagHom 2 K ⟨fieldSp 2 K σ (τε b), hfB⟩ =
        fun i => ((if ε then tauT (diagHom 2 K ⟨b, hb⟩) else diagHom 2 K ⟨b, hb⟩) i) ^ 2 ^ m := by
      rw [diagHom_fieldSp σ (hτεB hb)]
      funext i
      apply Units.ext
      rw [Units.coe_map, MonoidHom.coe_ofClass, hm, Units.val_pow_eq_pow_val]
      congr 2
      cases ε
      · rfl
      · exact congrFun (diagHom_tauSp hb) i
    rw [hw, map_mul, map_mul, map_mul, map_inv, hD, mul_comm (diagHom 2 K ⟨g, hgB⟩),
      mul_inv_cancel_right]
  rw [normalizer_projUnipotent (r := 2) (K := K) 2 (by norm_num)] at hkN hhN
  obtain ⟨bk, hbk, rfl⟩ := hkN
  obtain ⟨bh, hbh, rfl⟩ := hhN
  rw [hcrit bh hbh]
  rw [hcrit bk hbk] at hkinv
  have hbk3 : bk ^ 3 = 1 := hinj (by rw [map_pow, map_one, ← hk3, pow_orderOf_eq_one])
  have hbh3 : bh ^ 3 = 1 := hinj (by rw [map_pow, map_one, hh3])
  have hd3 : ∀ b (hb : b ∈ borelSubgroup 2 K), b ^ 3 = 1 → diagHom 2 K ⟨b, hb⟩ ^ 3 = 1 := by
    intro b hb h3
    rw [← map_pow]
    have : (⟨b, hb⟩ : borelSubgroup 2 K) ^ 3 = 1 := Subtype.ext (by simpa using h3)
    rw [this, map_one]
  have hdk1 : diagHom 2 K ⟨bk, hbk⟩ ≠ 1 := by
    intro h1
    have hU : bk ∈ unipotent 2 K := (diagHom_eq_one_iff _).mp h1
    obtain ⟨P2, hP2⟩ := exists_sylow_unipotent (K := K) 2 2
    have hP2' : bk ∈ (P2 : Subgroup (StatedSp 2 K)) := by rw [hP2]; exact hU
    obtain ⟨j, hj⟩ := P2.isPGroup' ⟨bk, hP2'⟩
    have hbkj : bk ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hdvd : orderOf (proj 2 K bk) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one (by
      rw [← map_pow, hbkj, map_one])
    rw [hk3] at hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hdvd)
    omega
  exact arith5 ε (hd3 bk hbk hbk3) hdk1 hkinv (hd3 bh hbh hbh3)

theorem clause5 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (hX : StatedClassicalModel X .PSp 2 2 f) (P : Sylow 2 X) (α : MulAut X)
    (hαP : ∀ x ∈ (P : Subgroup X), α x ∈ (P : Subgroup X))
    (k : X) (hkN : k ∈ Subgroup.normalizer ((P : Subgroup X) : Set X)) (hk3 : orderOf k = 3)
    (hkinv : α k * k ∈ (P : Subgroup X))
    (h : X) (hhN : h ∈ Subgroup.normalizer ((P : Subgroup X) : Set X)) (hh3 : h ^ 3 = 1) :
    α h * h ∈ (P : Subgroup X) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have : CharP K 2 := charP_two_of_card hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ := exists_sylow_projUnipotent (r := 2) (K := K) 2 (by norm_num)
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_sylow e P U
  rw [hU] at hφ
  have hαP' : ∀ x, α x ∈ (P : Subgroup X) ↔ x ∈ (P : Subgroup X) :=
    Sp4.mem_iff_of_forall_mem α _ hαP
  set α' := MulAut.congr φ α with hα'
  have hα'app : ∀ y, α' y = φ (α (φ.symm y)) := fun _ => rfl
  have hα'U : ∀ y, α' y ∈ projUnipotent 2 K ↔ y ∈ projUnipotent 2 K := by
    intro y
    rw [hα'app, ← hφ, hαP', hφ, MulEquiv.apply_symm_apply]
  have hN := mem_normalizer_iff_of_mulEquiv φ hφ
  have key : ∀ x, α' (φ x) * φ x = φ (α x * x) := by
    intro x
    rw [hα'app, MulEquiv.symm_apply_apply, map_mul]
  have h5 := model5 (n := f) (by omega) hK hα'U ((hN k).mp hkN)
    ((orderOf_injective φ.toMonoidHom φ.injective k).trans hk3) (by rw [key, ← hφ]; exact hkinv)
    ((hN h).mp hhN) (by rw [← map_pow, hh3, map_one])
  rw [key, ← hφ] at h5
  exact h5

end CFSG.Quasithin.H13.A5.SpBorel
