module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIO1Step1

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.QuasithinUnique.A5.Delta5

open scoped commutatorElement

set_option linter.unusedSectionVars false

section Generic5

theorem card_modEq_centralizer_five {G : Type*} [Group G] [Finite G] {V : Subgroup G} {f : G}
    (hf : ∀ z ∈ V, f * z * f⁻¹ ∈ V) (hf5 : f ^ 5 = 1) :
    Nat.card V ≡ Nat.card (V ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) [MOD 5] := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let σ : Function.End V := fun z => ⟨f * z * f⁻¹, hf z z.2⟩
  have h5 : ∀ (n : ℕ) (z : V), ((σ ^ n) z : G) = f ^ n * z * (f ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro z; simp; rfl
    | succ n ih =>
      intro z
      rw [pow_succ]
      show (((σ ^ n) (σ z) : V) : G) = _
      rw [ih]
      show f ^ n * (f * (z : G) * f⁻¹) * (f ^ n)⁻¹ = _
      simp only [pow_succ]
      group
  have hσ : σ ^ 5 ^ 1 = 1 := by
    rw [pow_one]
    funext z
    apply Subtype.ext
    have := h5 5 z
    rw [hf5] at this
    rw [this]
    simp
    rfl
  have : Fintype V := Fintype.ofFinite V
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := V) (f := σ) (p := 5) (n := 1) hσ
  have e : (Function.fixedPoints σ : Set V) ≃ (V ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) :=
    { toFun := fun z => ⟨z.1.1, z.1.2, by
        have h2 : f * (z.1 : G) * f⁻¹ = z.1 := congrArg Subtype.val z.2
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        calc (z.1 : G) * f = (f * z.1 * f⁻¹) * f := by rw [h2]
          _ = f * z.1 := by group⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, by
        apply Subtype.ext
        have h3 : (z.1 : G) * f = f * z.1 := Subgroup.mem_centralizer_singleton_iff.mp z.2.2
        show f * z.1 * f⁻¹ = z.1
        rw [← h3]; group⟩
      left_inv := fun z => rfl
      right_inv := fun z => rfl }
  have : Fintype ↥(V ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) := Fintype.ofFinite _
  have : Fintype ↑(Function.fixedPoints σ) := Fintype.ofFinite _
  have hc : Fintype.card ↑(Function.fixedPoints σ) =
      Fintype.card ↥(V ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) := Fintype.card_congr e
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← hc]
  convert hmod using 2


theorem comm_alg {R : Type*} [CommGroup R] {a0 a1 a2 a3 a4 : R} (h1 : a1 * a1 = 1)
    (h3 : a3 * a3 = 1) (hrel : a0 * a1 * a2 * a3 * a4 = 1) : a4 * a2 * a0 = a3 * a1 := by
  calc a4 * a2 * a0 = (a3 * a3) * (a1 * a1) * (a0 * a2 * a4) := by
        rw [h3, h1, one_mul, one_mul]; ac_rfl
    _ = a3 * a1 * (a0 * a1 * a2 * a3 * a4) := by ac_rfl
    _ = a3 * a1 := by rw [hrel, mul_one]

theorem decomp_alg {G : Type*} [Group G] {Z : Subgroup G} {f m : G}
    (hZf : ∀ k : ℕ, ∀ z ∈ Z, f ^ k * z * (f ^ k)⁻¹ ∈ Z)
    (hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZsq : ∀ a ∈ Z, a * a = 1)
    (hn : ⁅m, f⁆ ∈ Z) (hf5 : f ^ 5 = 1) :
    ∃ z ∈ Z, f * (z * m) * f⁻¹ = z * m := by
  set n : G := ⁅m, f⁆ with hn'
  have ha : ∀ k : ℕ, f ^ k * n * (f ^ k)⁻¹ ∈ Z := fun k => hZf k n hn
  have hrel : n * (f ^ 1 * n * (f ^ 1)⁻¹) * (f ^ 2 * n * (f ^ 2)⁻¹) * (f ^ 3 * n * (f ^ 3)⁻¹) *
      (f ^ 4 * n * (f ^ 4)⁻¹) = 1 := by
    have e : n * (f ^ 1 * n * (f ^ 1)⁻¹) * (f ^ 2 * n * (f ^ 2)⁻¹) * (f ^ 3 * n * (f ^ 3)⁻¹) *
        (f ^ 4 * n * (f ^ 4)⁻¹) = ⁅m, f ^ 5⁆ := by
      simp only [hn', commutatorElement_def]
      rw [show f ^ 5 = f * f * f * f * f by simp [pow_succ]]
      group
    rw [e, hf5]
    simp [commutatorElement_def]
  let _ : CommGroup ↥Z := { (inferInstance : Group ↥Z) with
    mul_comm := fun a b => Subtype.ext (hZcomm _ a.2 _ b.2) }
  have hmem0 : n ∈ Z := hn
  have hcomm := comm_alg (R := ↥Z) (a0 := ⟨n, hn⟩) (a1 := ⟨f ^ 1 * n * (f ^ 1)⁻¹, ha 1⟩)
    (a2 := ⟨f ^ 2 * n * (f ^ 2)⁻¹, ha 2⟩) (a3 := ⟨f ^ 3 * n * (f ^ 3)⁻¹, ha 3⟩)
    (a4 := ⟨f ^ 4 * n * (f ^ 4)⁻¹, ha 4⟩)
    (Subtype.ext (hZsq _ (ha 1))) (Subtype.ext (hZsq _ (ha 3))) (Subtype.ext hrel)
  have hcomm' := congrArg Subtype.val hcomm
  simp only [Subgroup.coe_mul] at hcomm'
  refine ⟨(f ^ 3 * n * (f ^ 3)⁻¹) * (f ^ 1 * n * (f ^ 1)⁻¹),
    Z.mul_mem (ha 3) (ha 1), ?_⟩
  have hnn : n⁻¹ = n := inv_eq_of_mul_eq_one_right (hZsq n hn)
  have hfm : f * m * f⁻¹ = n⁻¹ * m := by
    rw [hn']; simp only [commutatorElement_def]; group
  calc f * ((f ^ 3 * n * (f ^ 3)⁻¹) * (f ^ 1 * n * (f ^ 1)⁻¹) * m) * f⁻¹
      = (f * ((f ^ 3 * n * (f ^ 3)⁻¹) * (f ^ 1 * n * (f ^ 1)⁻¹)) * f⁻¹) * (f * m * f⁻¹) := by group
    _ = ((f ^ 4 * n * (f ^ 4)⁻¹) * (f ^ 2 * n * (f ^ 2)⁻¹)) * (n⁻¹ * m) := by
        rw [hfm]; congr 1; group
    _ = ((f ^ 4 * n * (f ^ 4)⁻¹) * (f ^ 2 * n * (f ^ 2)⁻¹) * n) * m := by rw [hnn]; group
    _ = _ := by rw [hcomm']

end Generic5

section Step2

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

variable (F : Frame L1 L2 S D X)
include F

theorem exists_five_elt : ∃ f ∈ P2 L1 L2 S, f ^ 5 = 1 ∧ f ∉ Q2 L1 L2 S := by
  obtain ⟨φ, hφs, hφk, -⟩ := exists_phi_Q1_surj F
  obtain ⟨ρ, hρ5, hρ1⟩ : ∃ ρ : Alt5, ρ ^ 5 = 1 ∧ ρ ≠ 1 := by decide +kernel
  obtain ⟨p, hp⟩ := hφs ρ
  have hp5 : ((p ^ 5 : ↥(P2 L1 L2 S)) : G) ∈ Q2 L1 L2 S :=
    (hφk _).mp (by rw [map_pow, hp, hρ5])
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (P2 L1 L2 S) ⟨((p ^ 5 : ↥(P2 L1 L2 S)) : G), hp5⟩
  have hk' : (((p : G)) ^ 5) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨(p : G) ^ 2 ^ k, (P2 L1 L2 S).pow_mem p.2 _, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]; exact hk'
  · intro hfQ
    have h1 : φ (p ^ 2 ^ k) = 1 := (hφk _).mpr hfQ
    rw [map_pow, hp] at h1
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hord : orderOf ρ = 5 := orderOf_eq_prime hρ5 hρ1
    have : 5 ∣ 2 ^ k := hord ▸ orderOf_dvd_of_pow_eq_one h1
    have h52 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five this
    omega

theorem five_acts_nontrivially (h : O1Hyp L1 L2 S) {f : G} (hf : f ∈ P2 L1 L2 S)
    (hfQ : f ∉ Q2 L1 L2 S) : ∃ z ∈ Z2q L1 L2 S, f * z ≠ z * f := by
  by_contra hall
  push Not at hall
  obtain ⟨φ, hφs, hφk, T, hT4, hlift, hN⟩ := exists_phi_Q1_surj F
  set Cc : Subgroup ↥(P2 L1 L2 S) :=
    (Subgroup.centralizer (Z2q L1 L2 S : Set G)).subgroupOf (P2 L1 L2 S) with hCc
  have hmemC : ∀ y : ↥(P2 L1 L2 S), y ∈ Cc ↔ ∀ z ∈ Z2q L1 L2 S, (y : G) * z = z * y := by
    intro y
    rw [hCc, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    exact ⟨fun h z hz => (h z hz).symm, fun h z hz => (h z hz).symm⟩
  have hCn : Cc.Normal := ⟨fun n hn p => by
    rw [hmemC] at hn ⊢
    intro z hz
    have hz' : (p : G)⁻¹ * z * p ∈ Z2q L1 L2 S := by
      simpa using Z2q_normal ((P2 L1 L2 S).inv_mem p.2) hz
    have h1 := hn _ hz'
    have e : ((p * n * p⁻¹ : ↥(P2 L1 L2 S)) : G) = (p : G) * n * (p : G)⁻¹ := by simp
    rw [e]
    calc (p : G) * n * (p : G)⁻¹ * z = (p : G) * (n * ((p : G)⁻¹ * z * p)) * (p : G)⁻¹ := by group
      _ = (p : G) * (((p : G)⁻¹ * z * p) * n) * (p : G)⁻¹ := by rw [h1]
      _ = z * ((p : G) * n * (p : G)⁻¹) := by group⟩
  have : IsSimpleGroup Alt5 := alternatingGroup.isSimpleGroup (by simp)
  have hmapn : (Cc.map φ).Normal := Subgroup.Normal.map hCn φ hφs
  have hf' : (⟨f, hf⟩ : ↥(P2 L1 L2 S)) ∈ Cc := (hmemC _).mpr (fun z hz => hall z hz)
  have htop : Cc.map φ = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Cc.map φ) with hb | ht
    · exfalso
      have : φ ⟨f, hf⟩ ∈ Cc.map φ := ⟨_, hf', rfl⟩
      rw [hb, Subgroup.mem_bot] at this
      exact hfQ ((hφk _).mp this)
    · exact ht
  obtain ⟨k, hkT, hk1⟩ : ∃ k ∈ T, k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : T = ⊥ := (Subgroup.eq_bot_iff_forall T).mpr hcon
    rw [this, Subgroup.card_bot] at hT4
    omega
  obtain ⟨q, hqQ1, hφq⟩ := hlift k hkT
  have hmem : φ q ∈ Cc.map φ := by rw [htop]; trivial
  obtain ⟨c, hc, hφc⟩ := hmem
  have hq' : ((c⁻¹ * q : ↥(P2 L1 L2 S)) : G) ∈ Q2 L1 L2 S := by
    apply (hφk _).mp
    rw [map_mul, map_inv, hφc]; group
  have hqcent : ∀ z ∈ Z2q L1 L2 S, (q : G) * z = z * q := by
    intro z hz
    have e : (q : G) = (c : G) * ((c⁻¹ * q : ↥(P2 L1 L2 S)) : G) := by simp
    rw [e]
    have h1 := (hmemC c).mp hc z hz
    have h2 := Z2q_comm F z hz _ hq'
    calc (c : G) * ((c⁻¹ * q : ↥(P2 L1 L2 S)) : G) * z
        = (c : G) * (((c⁻¹ * q : ↥(P2 L1 L2 S)) : G) * z) := by group
      _ = (c : G) * (z * ((c⁻¹ * q : ↥(P2 L1 L2 S)) : G)) := by rw [← h2]
      _ = ((c : G) * z) * ((c⁻¹ * q : ↥(P2 L1 L2 S)) : G) := by group
      _ = (z * (c : G)) * ((c⁻¹ * q : ↥(P2 L1 L2 S)) : G) := by rw [h1]
      _ = z * ((c : G) * ((c⁻¹ * q : ↥(P2 L1 L2 S)) : G)) := by group
  have hqS : (q : G) ∈ S := F.Q1_le_S hqQ1
  have hqQ2 : (q : G) ∈ Q2 L1 L2 S := h.faith _ hqS hqcent
  apply hk1
  rw [← hφq]
  exact (hφk q).mpr hqQ2


theorem C_Z2_five_trivial (h : O1Hyp L1 L2 S) {f : G} (hf : f ∈ P2 L1 L2 S) (hf5 : f ^ 5 = 1)
    (hfQ : f ∉ Q2 L1 L2 S) : ∀ z ∈ Z2q L1 L2 S, f * z = z * f → z = 1 := by
  have hmod := card_modEq_centralizer_five (V := Z2q L1 L2 S) (f := f)
    (fun z hz => Z2q_normal hf hz) hf5
  rw [h.card16] at hmod
  set C : Subgroup G := Z2q L1 L2 S ⊓ Subgroup.centralizer ({f} : Set G) with hC
  have hdvd : Nat.card C ∣ 2 ^ 4 := by
    have h2 : Nat.card C ∣ Nat.card (Z2q L1 L2 S) := Subgroup.card_dvd_of_le inf_le_left
    rw [h.card16] at h2
    exact (by norm_num : (16 : ℕ) = 2 ^ 4) ▸ h2
  obtain ⟨i, hi, hCi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hcases : Nat.card C = 1 ∨ Nat.card C = 16 := by
    have hmod' : 16 % 5 = Nat.card C % 5 := hmod
    rw [hCi] at hmod'
    have key : ∀ i : ℕ, i ≤ 4 → 16 % 5 = 2 ^ i % 5 → 2 ^ i = 1 ∨ 2 ^ i = 16 := by decide
    rw [hCi]
    exact key i hi hmod'
  intro z hz hzf
  have hzC : z ∈ C := ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr hzf.symm⟩
  rcases hcases with h1 | h16
  · have : C = ⊥ := (Subgroup.card_eq_one).mp h1
    rw [this, Subgroup.mem_bot] at hzC
    exact hzC
  · exfalso
    have heq : C = Z2q L1 L2 S :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : C ≤ Z2q L1 L2 S) (by rw [h16, h.card16])
    obtain ⟨z', hz', hne⟩ := five_acts_nontrivially F h hf hfQ
    have : z' ∈ C := heq ▸ hz'
    exact hne (Subgroup.mem_centralizer_singleton_iff.mp this.2).symm

theorem decomp_Q2 (h : O1Hyp L1 L2 S) {g : G} (hg : g ∈ P1 L1 L2 S)
    (hgB : g ∉ bigB L1 L2 S) (hnot : NotLe L1 L2 S g) {f : G}
    (hf : f ∈ P2 L1 L2 S) (hf5 : f ^ 5 = 1) :
    ∀ m ∈ Q2 L1 L2 S, ∃ z ∈ Z2q L1 L2 S, ∃ c ∈ Q2 L1 L2 S, f * c * f⁻¹ = c ∧ m = z * c := by
  intro m hm
  have hn : ⁅m, f⁆ ∈ Z2q L1 L2 S := step1_main F h hg hgB hnot f hf hf5 m hm
  have hZf : ∀ k : ℕ, ∀ z ∈ Z2q L1 L2 S, f ^ k * z * (f ^ k)⁻¹ ∈ Z2q L1 L2 S :=
    fun k z hz => Z2q_normal ((P2 L1 L2 S).pow_mem hf k) hz
  have hZcomm : ∀ a ∈ Z2q L1 L2 S, ∀ b ∈ Z2q L1 L2 S, a * b = b * a :=
    fun a ha b hb => Z2q_comm F a ha b (Z2q_le_Q2 F hb)
  have hZsq := Z2q_sq F
  obtain ⟨z, hz, hfix⟩ := decomp_alg hZf hZcomm hZsq hn hf5
  refine ⟨z, hz, z * m, (Q2 L1 L2 S).mul_mem (Z2q_le_Q2 F hz) hm, hfix, ?_⟩
  rw [← mul_assoc, hZsq z hz, one_mul]

theorem y_mem_Z2 (h : O1Hyp L1 L2 S) {g : G} (hg : g ∈ P1 L1 L2 S)
    (hgB : g ∉ bigB L1 L2 S) (hnot : NotLe L1 L2 S g) {y : G}
    (hyQ1 : y ∈ Q1 L1 L2 S) (hyQ2 : y ∈ Q2 L1 L2 S) (hyc : ∀ q ∈ Q2 L1 L2 S, y * q = q * y)
    (hy2 : y * y = 1) : y ∈ Z2q L1 L2 S := by
  obtain ⟨z, hz, q', hq', hyzq⟩ := Q1_le_mul F h hg hgB hnot y hyQ1
  have hzsq := Z2q_sq F z hz
  have hzQ2 : z ∈ Q2 L1 L2 S := Z2q_le_Q2 F hz
  have hq'eq : q' = z * y := by
    have : q' = z⁻¹ * y := by rw [hyzq]; group
    rw [this, inv_eq_of_mul_eq_one_right hzsq]
  have hq'Q2 : q' ∈ Q2 L1 L2 S := by rw [hq'eq]; exact (Q2 L1 L2 S).mul_mem hzQ2 hyQ2
  have hq'c : ∀ q ∈ Q2 L1 L2 S, q' * q = q * q' := by
    intro q hq
    rw [hq'eq]
    have h1 := Z2q_comm F z hz q hq
    have h2 := hyc q hq
    calc z * y * q = z * (y * q) := by group
      _ = z * (q * y) := by rw [h2]
      _ = (z * q) * y := by group
      _ = (q * z) * y := by rw [h1]
      _ = q * (z * y) := by group
  have hq'S : q' ∈ S := F.Q2_le_S hq'Q2
  have hq'sq : q' * q' = 1 := by
    have hzy : z * y = y * z := (Z2q_comm F z hz y hyQ2)
    rw [hq'eq]
    calc z * y * (z * y) = z * (y * z) * y := by group
      _ = z * (z * y) * y := by rw [← hzy]
      _ = (z * z) * (y * y) := by group
      _ = 1 := by rw [hzsq, hy2, one_mul]
  have hq'Z : q' ∈ quasithinOmegaOneCenter S := by
    have hcent : q' ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      obtain ⟨z', hz', q'', hq'', rfl⟩ := S_eq_mul F h hg hgB hnot s hs
      calc z' * q'' * q' = z' * (q'' * q') := by group
        _ = z' * (q' * q'') := by rw [← hq'c q'' hq'']
        _ = (z' * q') * q'' := by group
        _ = (q' * z') * q'' := by rw [conjZ2q_comm F z' hz' q' hq']
        _ = q' * (z' * q'') := by group
    exact Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hq'S, hcent⟩, by rw [pow_two]; exact hq'sq⟩
  rw [hyzq]
  exact (Z2q L1 L2 S).mul_mem hz (Z_le_Z2q hq'Z)


theorem Q1_inf_Q2_le (h : O1Hyp L1 L2 S) {g : G} (hg : g ∈ P1 L1 L2 S)
    (hgB : g ∉ bigB L1 L2 S) (hnot : NotLe L1 L2 S g) :
    Q1 L1 L2 S ⊓ Q2 L1 L2 S ≤ Z2q L1 L2 S := by
  obtain ⟨f, hf, hf5, hfQ⟩ := exists_five_elt F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cf : Subgroup G := Q2 L1 L2 S ⊓ Subgroup.centralizer ({f} : Set G) with hCf
  set N : Subgroup G := Cf ⊓ Q1 L1 L2 S with hN
  have hmemCf : ∀ c : G, c ∈ Q2 L1 L2 S → f * c * f⁻¹ = c → c ∈ Cf := by
    intro c hc hfc
    refine ⟨hc, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc c * f = (f * c * f⁻¹) * f := by rw [hfc]
      _ = f * c := by group
  have hNtriv : N = ⊥ := by
    by_contra hne
    have hQp : IsPGroup 2 ↥(Q2 L1 L2 S) := pCoreOf_isPGroup 2 _
    have hnil : Group.IsNilpotent ↥(Q2 L1 L2 S) := hQp.isNilpotent
    set Nq : Subgroup ↥(Q2 L1 L2 S) := N.subgroupOf (Q2 L1 L2 S) with hNq
    have hNle : N ≤ Q2 L1 L2 S := fun x hx => hx.1.1
    have hNqn : Nq.Normal := ⟨fun n hn q => by
      rw [hNq, Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨z, hz, c, hc, hfc, hqzc⟩ := decomp_Q2 F h hg hgB hnot hf hf5 q q.2
      have hzQ2 : z ∈ Q2 L1 L2 S := Z2q_le_Q2 F hz
      have hcnQ : (c : G) * n * c⁻¹ ∈ Q2 L1 L2 S :=
        (Q2 L1 L2 S).mul_mem ((Q2 L1 L2 S).mul_mem hc (hNle hn)) ((Q2 L1 L2 S).inv_mem hc)
      have e : ((q * n * q⁻¹ : ↥(Q2 L1 L2 S)) : G) = c * n * c⁻¹ := by
        have e1 : ((q * n * q⁻¹ : ↥(Q2 L1 L2 S)) : G) = (q : G) * n * (q : G)⁻¹ := by simp
        rw [e1, hqzc]
        have hzc := Z2q_comm F z hz (c * n * c⁻¹) hcnQ
        calc z * c * n * (z * c)⁻¹ = z * (c * n * c⁻¹) * z⁻¹ := by group
          _ = (c * n * c⁻¹) * z * z⁻¹ := by rw [hzc]
          _ = c * n * c⁻¹ := by group
      rw [e]
      refine ⟨(Cf).mul_mem ((Cf).mul_mem (hmemCf c hc hfc) hn.1) ((Cf).inv_mem (hmemCf c hc hfc)), ?_⟩
      have hcS : c ∈ S := F.Q2_le_S hc
      have := (Subgroup.mem_normalizer_iff.mp (P1_le_normalizer_Q1 L1 L2 S (F.mem_P1_of_mem_S hcS)) n).mp hn.2
      exact this⟩
    have hNq1 : Nq ≠ ⊥ := by
      intro hbot
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hNle hx⟩ : ↥(Q2 L1 L2 S)) ∈ Nq := Subgroup.mem_subgroupOf.mpr hx
      rw [hbot, Subgroup.mem_bot] at this
      have : x = 1 := congrArg Subtype.val this
      rw [this]; exact Subgroup.one_mem _
    have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hNq1
    obtain ⟨⟨x₀, hx₀⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcen
    have hx₀1 : x₀ ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQp) x₀
    have hk1 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero, orderOf_eq_one_iff] at hk
      exact hx₀1 hk
    have h2dvd : 2 ∣ orderOf x₀ := by
      rw [hk]; exact dvd_pow_self 2 hk1
    have hord : orderOf (x₀ ^ (orderOf x₀ / 2)) = 2 :=
      orderOf_pow_orderOf_div (orderOf_pos x₀).ne' h2dvd
    set y₀ : ↥(Q2 L1 L2 S) := x₀ ^ (orderOf x₀ / 2) with hy₀
    have hy₀sq : y₀ * y₀ = 1 := by
      rw [← pow_two, ← hord]; exact pow_orderOf_eq_one y₀
    have hy₀1 : y₀ ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord
      omega
    have hy₀mem : y₀ ∈ Nq ⊓ Subgroup.center ↥(Q2 L1 L2 S) := (Nq ⊓ _).pow_mem hx₀ _
    obtain ⟨hy₀N, hy₀C⟩ := hy₀mem
    have hy₀N' : (y₀ : G) ∈ N := hy₀N
    set y : G := (y₀ : G) with hy
    have hyc : ∀ q ∈ Q2 L1 L2 S, y * q = q * y := by
      intro q hq
      have := Subgroup.mem_center_iff.mp hy₀C ⟨q, hq⟩
      exact (congrArg Subtype.val this).symm
    have hy2 : y * y = 1 := by
      have := congrArg Subtype.val hy₀sq
      simpa using this
    have hyZ := y_mem_Z2 F h hg hgB hnot hy₀N'.2 y₀.2 hyc hy2
    have hyf := (Subgroup.mem_centralizer_singleton_iff.mp hy₀N'.1.2)
    have := C_Z2_five_trivial F h hf hf5 hfQ y hyZ hyf.symm
    apply hy₀1
    exact Subtype.ext this
  intro m hm
  obtain ⟨hmQ1, hmQ2⟩ := hm
  obtain ⟨z, hz, c, hc, hfc, hmzc⟩ := decomp_Q2 F h hg hgB hnot hf hf5 m hmQ2
  have hcQ1 : c ∈ Q1 L1 L2 S := by
    have : c = z⁻¹ * m := by rw [hmzc]; group
    rw [this]
    exact (Q1 L1 L2 S).mul_mem ((Q1 L1 L2 S).inv_mem (Z2q_le_Q1 F hz)) hmQ1
  have hcN : c ∈ N := ⟨hmemCf c hc hfc, hcQ1⟩
  rw [hNtriv, Subgroup.mem_bot] at hcN
  rw [hmzc, hcN, mul_one]
  exact hz

theorem card_Q1 : Nat.card (Q1 L1 L2 S) = 4 * Nat.card (Q1 L1 L2 S ⊓ Q2 L1 L2 S : Subgroup G) := by
  obtain ⟨φ, hφk, T, hT4, hTin, hlift, hN⟩ := exists_phi_Q1 F
  have hQP : Q1 L1 L2 S ≤ P2 L1 L2 S := fun q hq =>
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) (Q1_le_B F hq)
  set Q₁₀ : Subgroup ↥(P2 L1 L2 S) := (Q1 L1 L2 S).subgroupOf (P2 L1 L2 S) with hQ₁₀
  have hmap : Q₁₀.map φ = T := by
    apply le_antisymm
    · rintro _ ⟨q, hq, rfl⟩
      exact hTin q hq
    · intro k hk
      obtain ⟨q, hq, hφq⟩ := hlift k hk
      exact ⟨q, hq, hφq⟩
  have h1 := card_map_mul_card_inf φ Q₁₀
  have hkerQ : φ.ker = (Q2 L1 L2 S).subgroupOf (P2 L1 L2 S) := by
    ext p; rw [MonoidHom.mem_ker, hφk]; rfl
  have hinf : Q₁₀ ⊓ φ.ker = (Q1 L1 L2 S ⊓ Q2 L1 L2 S).subgroupOf (P2 L1 L2 S) := by
    ext p; rw [hkerQ]; simp [hQ₁₀, Subgroup.mem_subgroupOf]
  rw [hmap, hT4, hinf, natCard_subgroupOf' (inf_le_left.trans hQP), natCard_subgroupOf' hQP] at h1
  omega

end Step2

end CFSG.Quasithin.Kleidman.F204
