module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelSUTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

namespace SUModel

variable {f : ℕ} {K : Type} [Field K] {G : Type} [Group G]

theorem twistNorm_one {m : ℕ} (σ : K ≃+* K) (k : ℕ) :
    LinModel.twistNorm (1 : GL (Fin (m + 1)) K) σ k = 1 := by
  induction k with
  | zero => exact LinModel.twistNorm_zero _ _
  | succ k ih => rw [LinModel.twistNorm_succ, ih, map_one, one_mul]

theorem glAut_diagHom_eq {n p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {τ : K ≃+* K} {k : ℕ} (hτ : τ ^ (p ^ k) = 1) {d : Fin n → Kˣ} (hd : ∀ i, d i ^ p = 1) :
    glAut τ (diagHom n d) = diagHom n d := by
  apply Units.ext
  rw [coe_glAut, coe_diagHom, diagonal_map (map_zero τ)]
  congr 1
  funext i
  exact LinModel.fieldAut_fixes_root hp hζ hτ (by
    rw [← Units.val_pow_eq_pow_val, hd i, Units.val_one])

variable (h : UnitaryFieldData 2 f K) {m : ℕ} {φ : ↥(unitarySU 2 f K (m + 1)) →* G}
  (hn : 3 ≤ m + 1) (hq : ¬(m + 1 = 3 ∧ 2 ^ f = 2))
  (hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)))
  (hC : Subgroup.centralizer (φ.range : Set G) = ⊥)

include hn hq hker hC in
theorem exists_mem_suPairs_of_pow_pow_eq_one {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    (hreal : ∀ A ∈ primeFormUnitary h (idGram K (m + 1)), ∃ g : G, (g, A) ∈ SUTorus.suPairs φ)
    {Bs : Subgroup G} (hBs : UnitModel.frameTorus p h φ = Bs)
    (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {u : G} (hu : u ∈ Subgroup.normalizer (φ.range : Set G)) {k : ℕ} (huk : u ^ (p ^ k) = 1) :
    ∃ A : GL (Fin (m + 1)) K, A ∈ primeFormUnitary h (idGram K (m + 1)) ∧
      (u, A) ∈ SUTorus.suPairs φ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, σ, hA⟩ := exists_semiActs h hn hq hker hC hu
  have hσk : σ ^ (p ^ k) = 1 := by
    have h1 := hA.pow (p ^ k)
    rw [huk] at h1
    exact eq_of_semiActs hn hq hker hC h1 (semiActs_one φ)
  by_cases hσ1 : σ = 1
  · rw [hσ1] at hA
    exact ⟨A, semiActs_one_iff.mp hA⟩
  exfalso
  obtain ⟨ζ₀, hζ₀, -⟩ := CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one h hp hpq
  have hζ : IsPrimitiveRoot (ζ₀ : K) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hζ₀)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hσk)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, pow_zero, orderOf_eq_one_iff] at hj
      exact absurd hj hσ1
    · exact ⟨j - 1, by omega⟩
  set τ := σ ^ (p ^ i) with hτdef
  have hτp : τ ^ p = 1 := by
    rw [hτdef, ← pow_mul, ← pow_succ, ← hj, pow_orderOf_eq_one]
  have hτ1 : τ ≠ 1 := by
    intro h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hj] at h2
    have h3 := Nat.le_of_dvd (pow_pos hp.pos _) h2
    have h4 := Nat.pow_lt_pow_right hp.one_lt (show i < i + 1 by omega)
    omega
  have hu' := hA.pow (p ^ i)
  obtain ⟨g₀, hg₀⟩ := hreal _ ((primeFormUnitary h _).inv_mem hu'.1)
  have hg₀' : SemiActs h φ g₀ (LinModel.twistNorm A σ (p ^ i))⁻¹ 1 :=
    semiActs_one_iff.mpr ⟨(primeFormUnitary h _).inv_mem hu'.1, hg₀⟩
  set g := g₀ * u ^ (p ^ i) with hgdef
  have hg : SemiActs h φ g 1 τ := by
    have h1 := hg₀'.mul hu'
    rwa [glAut_one_apply, inv_mul_cancel, one_mul] at h1
  have hgp : g ^ p = 1 := by
    have h1 := hg.pow p
    rw [twistNorm_one, hτp] at h1
    have h2 := SUTorus.mem_centralizer_of_mem_suPairs_one (semiActs_one_iff.mp h1).2
    rwa [hC, Subgroup.mem_bot] at h2
  have hgC : g ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hBs] at hb
    obtain ⟨d, hd, hbd⟩ := hb
    have hb' := semiActs_of_frameActs (h := h) hbd
    have e1 := hg.mul hb'
    have e2 := hb'.mul hg
    rw [glAut_diagHom_eq hp hζ (k := 1) (by rw [pow_one]; exact hτp) hd, one_mul,
      mul_one] at e1
    rw [glAut_one_apply, mul_one, one_mul] at e2
    refine (SURep.eq_of_act_eqU hC fun s => ?_).symm
    rw [e1.apply s, e2.apply s]
  have hgB := hom g hgC hgp
  rw [← hBs] at hgB
  obtain ⟨e, -, hge⟩ := hgB
  exact hτ1 (eq_of_semiActs hn hq hker hC hg (semiActs_of_frameActs (h := h) hge))


omit hn hq hker hC

include h in
theorem mem_suPairs_of_frameActs {n : ℕ} {φ : ↥(unitarySU 2 f K n) →* G} {g : G}
    {τ : Fin n → Kˣ} (hg : SURep.GGFrameActs φ g τ) : (g, diagHom n τ) ∈ SUTorus.suPairs φ :=
  (semiActs_one_iff.mp (semiActs_of_frameActs (h := h) hg)).2

theorem commute_of_mem_suPairs_diag {n : ℕ} {φ : ↥(unitarySU 2 f K n) →* G}
    (hC : Subgroup.centralizer (φ.range : Set G) = ⊥) {g g' : G} {d e : Fin n → Kˣ}
    (hg : (g, diagHom n d) ∈ SUTorus.suPairs φ) (hg' : (g', diagHom n e) ∈ SUTorus.suPairs φ) :
    g * g' = g' * g := by
  have h1 := (SUTorus.suPairs φ).mul_mem ((SUTorus.suPairs φ).mul_mem hg hg')
    ((SUTorus.suPairs φ).inv_mem ((SUTorus.suPairs φ).mul_mem hg' hg))
  rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk, ← map_mul, ← map_mul,
    mul_comm d e, mul_inv_cancel] at h1
  have h2 := SUTorus.mem_centralizer_of_mem_suPairs_one h1
  rw [hC, Subgroup.mem_bot, mul_inv_eq_one] at h2
  exact h2

theorem mem_frameTorus_of_mulSingle {n p : ℕ} {φ : ↥(unitarySU 2 f K n) →* G} {ω : Kˣ}
    (hωp : ω ^ p = 1) {l : Fin n} {g : G} (hg : SURep.GGFrameActs φ g (Pi.mulSingle l ω)) :
    g ∈ UnitModel.frameTorus p h φ := by
  refine ⟨_, fun k => ?_, hg⟩
  by_cases hk : k = l
  · rw [hk, Pi.mulSingle_eq_same, hωp]
  · rw [Pi.mulSingle_eq_of_ne hk, one_pow]

include hn hq hker in
theorem eq_of_ne_zero_of_mem_normalizer {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    {ω : Kˣ} (hω1 : ω ≠ 1) (hωp : ω ^ p = 1)
    (hreal1 : ∀ l : Fin (m + 1), ∃ g : G, SURep.GGFrameActs φ g (Pi.mulSingle l ω))
    {Bs : Subgroup G} (hBs : UnitModel.frameTorus p h φ = Bs) {u : G}
    (hu : u ∈ Subgroup.normalizer (Bs : Set G)) {A : GL (Fin (m + 1)) K}
    (hA : (u, A) ∈ SUTorus.suPairs φ) {i l l' : Fin (m + 1)}
    (hl : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) l i ≠ 0)
    (hl' : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) l' i ≠ 0) : l = l' := by
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => hq ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  refine LinModel.eq_of_ne_zero_of_mul_diagGL hω1 (fun l => ?_) hl hl'
  obtain ⟨g, hg⟩ := hreal1 l
  have hgBs : g ∈ Bs := by
    rw [← hBs]
    exact mem_frameTorus_of_mulSingle h hωp hg
  have hb : u⁻¹ * g * u ∈ Bs := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hu) g).mp hgBs
    rwa [inv_inv] at this
  rw [← hBs] at hb
  obtain ⟨e, -, hbe⟩ := hb
  have h1 := (SUTorus.suPairs φ).mul_mem ((SUTorus.suPairs φ).mul_mem hA
    (mem_suPairs_of_frameActs h hbe)) ((SUTorus.suPairs φ).inv_mem hA)
  rw [Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk,
    show u * (u⁻¹ * g * u) * u⁻¹ = g by group] at h1
  obtain ⟨κ, hκ⟩ := SUTorus.exists_scalar_mul_of_mem_suPairs h hn hnq hp hpq hker
    (mem_suPairs_of_frameActs h hg) h1
  rw [diagHom_eq_diagGL, diagHom_eq_diagGL, LinModel.scalar_mul_diagGL] at hκ
  refine ⟨κ, e, ?_⟩
  rw [← hκ]
  group

theorem perm_eq_one_of_mul_diagGL (hm : 2 ≤ m) {A : GL (Fin (m + 1)) K}
    {π : Equiv.Perm (Fin (m + 1))}
    (hπ : LinModel.IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) π) {ω : Kˣ}
    (hω1 : ω ≠ 1) (hcomm : ∀ i, ∃ κ : Kˣ, A * InnerDiagA.diagGL (Pi.mulSingle i ω) =
      InnerDiagA.diagGL (fun k => κ * (Pi.mulSingle i ω : Fin (m + 1) → Kˣ) k) * A) :
    π = 1 := by
  ext i
  by_contra hπi
  have hπi' : π i ≠ i := fun h => hπi (by rw [h]; rfl)
  obtain ⟨κ, h2⟩ := hcomm i
  have h3 := congrArg (fun X : GL (Fin (m + 1)) K => (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K))
    h2
  simp only [Units.val_mul, InnerDiagA.coe_diagGL] at h3
  have key : ∀ j, (((Pi.mulSingle i ω : Fin (m + 1) → Kˣ) j : Kˣ) : K) =
      (κ : K) * (((Pi.mulSingle i ω : Fin (m + 1) → Kˣ) (π j) : Kˣ) : K) := by
    intro j
    have hj := congrFun (congrFun h3 (π j)) j
    rw [mul_diagonal, diagonal_mul] at hj
    have h0 : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (π j) j ≠ 0 := (hπ j (π j)).mpr rfl
    exact mul_left_cancel₀ h0 (by rw [hj]; ring)
  obtain ⟨j, hji, hjπ⟩ : ∃ j, j ≠ i ∧ π j ≠ i := by
    have hcard : ({i, π.symm i} : Finset (Fin (m + 1))).card <
        (Finset.univ : Finset (Fin (m + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      have := Finset.card_insert_le i ({π.symm i} : Finset (Fin (m + 1)))
      rw [Finset.card_singleton] at this
      omega
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    refine ⟨j, fun h => hj (by rw [h]; exact Finset.mem_insert_self _ _), fun h => hj ?_⟩
    rw [← h, Equiv.symm_apply_apply]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hκ1 : (κ : K) = 1 := by
    have := key j
    rw [Pi.mulSingle_eq_of_ne hji, Pi.mulSingle_eq_of_ne hjπ, Units.val_one, mul_one] at this
    exact this.symm
  have := key i
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hπi', hκ1, Units.val_one, one_mul] at this
  exact hω1 (Units.ext (by rw [this, Units.val_one]))

include hn hq hker in
theorem perm_eq_one_of_mem_centralizer (hm : 2 ≤ m) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ f + 1) {ω : Kˣ} (hω1 : ω ≠ 1) (hωp : ω ^ p = 1)
    (hreal1 : ∀ l : Fin (m + 1), ∃ g : G, SURep.GGFrameActs φ g (Pi.mulSingle l ω))
    {Bs : Subgroup G} (hBs : UnitModel.frameTorus p h φ = Bs) {u : G}
    (hu : u ∈ Subgroup.centralizer (Bs : Set G)) {A : GL (Fin (m + 1)) K}
    (hA : (u, A) ∈ SUTorus.suPairs φ) {π : Equiv.Perm (Fin (m + 1))}
    (hπ : LinModel.IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) π) : π = 1 := by
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => hq ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  refine perm_eq_one_of_mul_diagGL hm hπ hω1 fun i => ?_
  obtain ⟨g, hg⟩ := hreal1 i
  have hgBs : g ∈ Bs := by
    rw [← hBs]
    exact mem_frameTorus_of_mulSingle h hωp hg
  have hcomm : u * g * u⁻¹ = g := by
    rw [(Subgroup.mem_centralizer_iff.mp hu g hgBs).symm, mul_inv_cancel_right]
  have h1 := (SUTorus.suPairs φ).mul_mem ((SUTorus.suPairs φ).mul_mem hA
    (mem_suPairs_of_frameActs h hg)) ((SUTorus.suPairs φ).inv_mem hA)
  rw [Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, hcomm] at h1
  obtain ⟨κ, hκ⟩ := SUTorus.exists_scalar_mul_of_mem_suPairs h hn hnq hp hpq hker
    (mem_suPairs_of_frameActs h hg) h1
  rw [diagHom_eq_diagGL, LinModel.scalar_mul_diagGL] at hκ
  refine ⟨κ, ?_⟩
  rw [← hκ]
  group


include hn hq hker hC in
theorem torus_clause_one [Finite G] {p : ℕ} (hp : p.Prime) (hmp : m + 1 = p)
    (hpq : p ∣ 2 ^ f + 1) {ω : Kˣ} (hω1 : ω ≠ 1) (hωp : ω ^ p = 1)
    (hreal1 : ∀ l : Fin (m + 1), ∃ g : G, SURep.GGFrameActs φ g (Pi.mulSingle l ω))
    {Bs : Subgroup G} (hBs : UnitModel.frameTorus p h φ = Bs)
    (hmat : ∀ u ∈ Subgroup.normalizer (Bs : Set G), (∃ k, u ^ (p ^ k) = 1) →
      ∃ A : GL (Fin (m + 1)) K, (u, A) ∈ SUTorus.suPairs φ)
    (Q : Subgroup G) (hQN : Q ≤ Subgroup.normalizer (Bs : Set G)) (hQp : IsPGroup p Q) :
    IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) ∧
      Nat.card Q ≤ p * Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => hq ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  have hm : 2 ≤ m := by omega
  have hmono : ∀ u ∈ Q, ∃ (π : Equiv.Perm (Fin (m + 1))) (A : GL (Fin (m + 1)) K),
      (u, A) ∈ SUTorus.suPairs φ ∧
        LinModel.IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) π := by
    intro u hu
    obtain ⟨k, hk⟩ := hQp ⟨u, hu⟩
    obtain ⟨A, hA⟩ := hmat u (hQN hu) ⟨k, by
      have := congrArg Subtype.val hk
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using this⟩
    obtain ⟨π, hπ⟩ := LinModel.exists_isPermOf (A := A) fun i l l' hl hl' =>
      eq_of_ne_zero_of_mem_normalizer h hn hq hker hp hpq hω1 hωp hreal1 hBs (hQN hu) hA hl hl'
    exact ⟨π, A, hA, hπ⟩
  choose π A hA hπ using hmono
  have hmul : ∀ u v : Q, π ((u * v : Q) : G) (u * v).2 = π u u.2 * π v v.2 := by
    intro u v
    have h1 := (SUTorus.suPairs φ).mul_mem (hA u u.2) (hA v v.2)
    obtain ⟨κ, hκ⟩ := SUTorus.exists_scalar_mul_of_mem_suPairs h hn hnq hp hpq hker h1
      (hA _ (u * v).2)
    have h2 : LinModel.IsPermOf (((A _ (u * v).2 : GL (Fin (m + 1)) K)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) (π u u.2 * π v v.2) := by
      rw [hκ]
      refine LinModel.IsPermOf.scalar_mul ?_ κ
      rw [Units.val_mul]
      exact (hπ u u.2).mul (hπ v v.2)
    exact (hπ _ _).unique h2
  set Φ : Q →* Equiv.Perm (Fin (m + 1)) := MonoidHom.mk' (fun u => π u u.2) hmul with hΦ
  have hdiag : ∀ (u : G) (hu : u ∈ Q), π u hu = 1 →
      ∃ d : Fin (m + 1) → Kˣ, (u, diagHom (m + 1) d) ∈ SUTorus.suPairs φ := by
    intro u hu hu1
    have hπ1 := hπ u hu
    rw [hu1] at hπ1
    obtain ⟨d, hd⟩ := LinModel.IsPermOf.exists_eq_diagGL hπ1
    have hud := hA u hu
    rw [hd, ← diagHom_eq_diagGL] at hud
    exact ⟨d, hud⟩
  have hdiagC : ∀ (u : G) (hu : u ∈ Q), π u hu = 1 →
      u ∈ Subgroup.centralizer (Bs : Set G) := by
    intro u hu hu1
    obtain ⟨d, hud⟩ := hdiag u hu hu1
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hBs] at hb
    obtain ⟨e, -, hbe⟩ := hb
    exact commute_of_mem_suPairs_diag hC (mem_suPairs_of_frameActs h hbe) hud
  have hcard : Nat.card Q ≤ p * Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) := by
    rw [← Subgroup.card_ker_mul_card_range Φ]
    have hr : Nat.card Φ.range ≤ p := LinModel.card_le_of_isPGroup_perm hp hmp
      (IsPGroup.of_surjective hQp Φ.rangeRestrict Φ.rangeRestrict_surjective)
    have hk : Nat.card Φ.ker ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) := by
      have hle : (Φ.ker).map Q.subtype ≤ Q ⊓ Subgroup.centralizer (Bs : Set G) := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u.2, hdiagC u u.2 (MonoidHom.mem_ker.mp hu)⟩
      calc Nat.card Φ.ker = Nat.card ((Φ.ker).map Q.subtype) :=
            (Subgroup.card_map_of_injective Q.subtype_injective).symm
        _ ≤ _ := Subgroup.card_le_of_le hle
    calc Nat.card Φ.ker * Nat.card Φ.range ≤
          Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) * p := Nat.mul_le_mul hk hr
      _ = p * Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) := mul_comm _ _
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, hcard⟩
  obtain ⟨u, huQ, huC⟩ := x
  obtain ⟨v, hvQ, hvC⟩ := y
  have hd : ∀ (w : G) (hwQ : w ∈ Q), w ∈ Subgroup.centralizer (Bs : Set G) →
      ∃ d : Fin (m + 1) → Kˣ, (w, diagHom (m + 1) d) ∈ SUTorus.suPairs φ := fun w hwQ hwC =>
    hdiag w hwQ (perm_eq_one_of_mem_centralizer h hn hq hker hm hp hpq hω1 hωp hreal1 hBs hwC
      (hA w hwQ) (hπ w hwQ))
  obtain ⟨d, hud⟩ := hd u huQ huC
  obtain ⟨e, hve⟩ := hd v hvQ hvC
  exact commute_of_mem_suPairs_diag hC hud hve

end SUModel

end CFSG.StandardType
