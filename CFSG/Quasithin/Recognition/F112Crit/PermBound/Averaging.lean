module

public import CFSG.Quasithin.Recognition.F112Crit.PermBound.Basic
import Mathlib.Tactic.Abel
import TauCeti.Algebra.GroupAction.QuotientAddGroup
public import CFSG.Quasithin.Recognition.F112Crit.GaloisDescent
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.F112Crit.PermBound

variable {H : Type*} [Group H] {Ω : Type*} [MulAction H Ω] {M : Type*} [AddCommGroup M]
  [DistribMulAction H M]

open GaloisDescent

theorem smul_mem_commL {L : Subgroup H} {g : H} (hg : ∀ l ∈ L, g * l * g⁻¹ ∈ L) {k : M}
    (hk : k ∈ commL M L) : g • k ∈ commL M L := by
  induction hk using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, m, rfl⟩ := hx
    have : g • (l • m - m) = (g * l * g⁻¹) • (g • m) - g • m := by
      rw [smul_sub, smul_smul, smul_smul]
      simp [mul_assoc]
    rw [this]
    exact sub_mem_commL (hg l hl) _
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem commL_le_of_forall [Finite M] (h2 : ∀ m : M, m + m = 0) {L : Subgroup H}
    (hLodd : L ≤ Subgroup.closure {h : H | h ∈ L ∧ Odd (orderOf h)}) {Y : AddSubgroup M}
    (hY : ∀ l ∈ L, ∀ k ∈ commL M L, l • k - k ∈ Y) : commL M L ≤ Y := by
  let T : Subgroup H :=
    { carrier := {h | ∀ m : M, h • m - m ∈ Y}
      mul_mem' := fun {a b} ha hb m => by
        have : (a * b) • m - m = (a • (b • m) - b • m) + (b • m - m) := by rw [mul_smul]; abel
        rw [this]; exact add_mem (ha _) (hb m)
      one_mem' := fun m => by simp
      inv_mem' := fun {a} ha m => by
        have : a⁻¹ • m - m = -(a • (a⁻¹ • m) - a⁻¹ • m) := by rw [smul_inv_smul]; abel
        rw [this]; exact neg_mem (ha _) }
  have hodd : ∀ g ∈ L, Odd (orderOf g) → g ∈ T := by
    intro g hg hgo m
    let φ : M →+ M := AddMonoidHom.mk' (fun m => g • m - m) (fun a b => by rw [smul_add]; abel)
    have hφ : ∀ m, φ m = g • m - m := fun m => rfl
    have hRK : ∀ x ∈ φ.range, x ∈ commL M L := by
      rintro _ ⟨m, rfl⟩
      exact sub_mem_commL hg m
    have hinj : ∀ x ∈ φ.range, g • x - x = 0 → x = 0 := by
      rintro _ ⟨m, rfl⟩ h0
      have hgx : g • (g • m - m) = g • m - m := sub_eq_zero.mp h0
      have hpow : ∀ n : ℕ, (g ^ n) • m = m + n • (g • m - m) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', mul_smul, ih, smul_add, smul_comm g n, hgx, succ_nsmul]
          abel
      have h3 := hpow (orderOf g)
      rw [pow_orderOf_eq_one, one_smul] at h3
      have h4 : orderOf g • (g • m - m) = 0 := by
        have : m + orderOf g • (g • m - m) = m + 0 := by rw [← h3, add_zero]
        exact add_left_cancel this
      rwa [odd_nsmul_eq h2 (Nat.odd_iff.mp hgo)] at h4
    let f : φ.range → φ.range := fun x => ⟨φ x, x, rfl⟩
    have hfinj : Function.Injective f := by
      intro x y hxy
      have hxy' : φ x = φ y := congrArg Subtype.val hxy
      have h1 : g • ((x : M) - y) - ((x : M) - y) = 0 := by
        have : g • ((x : M) - y) - ((x : M) - y) = φ x - φ y := by
          rw [hφ, hφ, smul_sub]; abel
        rw [this, hxy', sub_self]
      exact Subtype.ext (sub_eq_zero.mp (hinj _ (φ.range.sub_mem x.2 y.2) h1))
    obtain ⟨y, hy⟩ := Finite.surjective_of_injective hfinj ⟨φ m, m, rfl⟩
    have hy' : φ y = φ m := congrArg Subtype.val hy
    show φ m ∈ Y
    rw [← hy', hφ]
    exact hY g hg y (hRK y y.2)
  have hLT : L ≤ T :=
    hLodd.trans ((Subgroup.closure_le T).2 fun g hg => hodd g hg.1 hg.2)
  refine (AddSubgroup.closure_le Y).2 ?_
  rintro _ ⟨l, hl, m, rfl⟩
  exact hLT hl m

theorem exists_fixed_mod_of_pow {G : Type*} [Group G] [DistribMulAction G M] [Finite M]
    (h2 : ∀ m : M, m + m = 0) {Z X : AddSubgroup M}
    (hZ : ∀ g : G, ∀ z ∈ Z, g • z ∈ Z) (hX : ∀ g : G, ∀ x ∈ X, g • x ∈ X)
    (hG : ∀ g : G, ∃ k : ℕ, ∀ z ∈ Z, (g ^ 2 ^ k) • z - z ∈ X) (hZX : ¬ Z ≤ X) :
    ∃ c ∈ Z, c ∉ X ∧ ∀ g : G, g • c - c ∈ X := by
  letI : DistribMulAction G (Z ⧸ X.addSubgroupOf Z) := X.subquotientDistribMulAction Z hX hZ
  have hsmul : ∀ (g : G) (z : Z), g • (z : Z ⧸ X.addSubgroupOf Z) =
      ((⟨g • (z : M), hZ g z z.2⟩ : Z) : Z ⧸ X.addSubgroupOf Z) := fun g z => rfl
  have hQ2 : ∀ q : Z ⧸ X.addSubgroupOf Z, q + q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H z =>
      rw [← QuotientAddGroup.mk_add, show z + z = 0 from Subtype.ext (h2 _),
        QuotientAddGroup.mk_zero]
  obtain ⟨z₀, hz₀Z, hz₀X⟩ := Set.not_subset.mp hZX
  have hq₀ : ((⟨z₀, hz₀Z⟩ : Z) : Z ⧸ X.addSubgroupOf Z) ≠ 0 := by
    intro h
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h
    exact hz₀X h
  have hdvd : 2 ∣ Nat.card (Z ⧸ X.addSubgroupOf Z) := by
    have h1 : addOrderOf ((⟨z₀, hz₀Z⟩ : Z) : Z ⧸ X.addSubgroupOf Z) = 2 :=
      addOrderOf_eq_prime (by rw [two_nsmul]; exact hQ2 _) hq₀
    rw [← h1]
    exact addOrderOf_dvd_natCard _
  have hPG : IsPGroup 2 (MulAction.toPermHom G (Z ⧸ X.addSubgroupOf Z)).range := by
    intro σ
    obtain ⟨g, hg⟩ := σ.2
    obtain ⟨k, hk⟩ := hG g
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hg, ← map_pow]
    ext q
    induction q using QuotientAddGroup.induction_on with
    | H z =>
      show (g ^ 2 ^ k) • (z : Z ⧸ X.addSubgroupOf Z) = z
      rw [hsmul, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
      exact hk z z.2
  have h0 : (0 : Z ⧸ X.addSubgroupOf Z) ∈
      MulAction.fixedPoints (MulAction.toPermHom G (Z ⧸ X.addSubgroupOf Z)).range
        (Z ⧸ X.addSubgroupOf Z) := by
    intro σ
    obtain ⟨g, hg⟩ := σ.2
    have hval : (σ • (0 : Z ⧸ X.addSubgroupOf Z)) = (σ : Equiv.Perm _) 0 := rfl
    rw [hval, ← hg]
    show g • (0 : Z ⧸ X.addSubgroupOf Z) = 0
    exact smul_zero g
  obtain ⟨b, hb, hne⟩ := hPG.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (Z ⧸ X.addSubgroupOf Z) hdvd h0
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective b
  refine ⟨(z : M), z.2, ?_, fun g => ?_⟩
  · intro hzX
    apply hne
    exact ((QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_addSubgroupOf.2 hzX)).symm
  · have h1 : g • (z : Z ⧸ X.addSubgroupOf Z) = z :=
      hb ⟨MulAction.toPermHom G _ g, g, rfl⟩
    rw [hsmul, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf] at h1
    exact h1

theorem mem_of_forall_smul_sub_mem [Finite M] (h2 : ∀ m : M, m + m = 0) {L : Subgroup H}
    (hLodd : L ≤ Subgroup.closure {h : H | h ∈ L ∧ Odd (orderOf h)})
    {P : Subgroup H} (hPL : P ≤ Subgroup.normalizer (L : Set H)) {X : AddSubgroup M}
    (hXK : X ≤ commL M L) (hXne : X ≠ commL M L) (hXL : ∀ l ∈ L, ∀ x ∈ X, l • x ∈ X)
    (hXP : ∀ p ∈ P, ∀ x ∈ X, p • x ∈ X)
    (hmax : ∀ Y : AddSubgroup M, Y ≤ commL M L → Y ≠ commL M L →
      (∀ l ∈ L, ∀ y ∈ Y, l • y ∈ Y) → (∀ p ∈ P, ∀ y ∈ Y, p • y ∈ Y) → X ≤ Y → Y ≤ X)
    {y : M} (hyK : y ∈ commL M L) (hy : ∀ l ∈ L, l • y - y ∈ X) : y ∈ X := by
  let Y : AddSubgroup M :=
    { carrier := {y | y ∈ commL M L ∧ ∀ l ∈ L, l • y - y ∈ X}
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun l hl => by
        have : l • (a + b) - (a + b) = (l • a - a) + (l • b - b) := by rw [smul_add]; abel
        rw [this]; exact add_mem (ha.2 l hl) (hb.2 l hl)⟩
      zero_mem' := ⟨zero_mem _, fun l hl => by simp⟩
      neg_mem' := fun {a} ha => ⟨neg_mem ha.1, fun l hl => by
        have : l • (-a) - -a = -(l • a - a) := by rw [smul_neg]; abel
        rw [this]; exact neg_mem (ha.2 l hl)⟩ }
  have hXY : X ≤ Y := fun x hx => ⟨hXK hx, fun l hl => sub_mem (hXL l hl x hx) hx⟩
  have hYK : Y ≤ commL M L := fun y hy => hy.1
  have hYL : ∀ l ∈ L, ∀ y ∈ Y, l • y ∈ Y := by
    intro l' hl' y hy
    refine ⟨smul_mem_commL (fun l hl => L.mul_mem (L.mul_mem hl' hl) (L.inv_mem hl')) hy.1,
      fun l hl => ?_⟩
    have : l • (l' • y) - l' • y = l' • ((l'⁻¹ * l * l') • y - y) := by
      simp [smul_sub, smul_smul, mul_assoc]
    rw [this]
    exact hXL l' hl' _ (hy.2 _ (L.mul_mem (L.mul_mem (L.inv_mem hl') hl) hl'))
  have hYP : ∀ p ∈ P, ∀ y ∈ Y, p • y ∈ Y := by
    intro p hp y hy
    refine ⟨smul_mem_commL (fun l hl => (Subgroup.mem_normalizer_iff.mp (hPL hp) l).mp hl) hy.1,
      fun l hl => ?_⟩
    have hl' : p⁻¹ * l * p ∈ L := by
      have h := (Subgroup.mem_normalizer_iff.mp (hPL (P.inv_mem hp)) l).mp hl
      rwa [inv_inv] at h
    have : l • (p • y) - p • y = p • ((p⁻¹ * l * p) • y - y) := by
      simp [smul_sub, smul_smul, mul_assoc]
    rw [this]
    exact hXP p hp _ (hy.2 _ hl')
  by_cases hYe : Y = commL M L
  · exfalso
    have hKX : commL M L ≤ X := commL_le_of_forall h2 hLodd (Y := X) fun l hl k hk => by
      have hk' : k ∈ Y := by rw [hYe]; exact hk
      exact hk'.2 l hl
    exact hXne (le_antisymm hXK hKX)
  · exact hmax Y hYK hYe hYL hYP hXY ⟨hyK, hy⟩

theorem exists_commL_fixed [Finite Ω] [Finite M] (h2 : ∀ m : M, m + m = 0) {L : Subgroup H}
    (htrans : ∀ μ ν : Ω, ∃ l ∈ L, l • μ = ν) (hodd : Odd (Nat.card Ω))
    (V : Ω → AddSubgroup M) (hV : ∀ l ∈ L, ∀ μ : Ω, ∀ v ∈ V μ, l • v ∈ V (l • μ))
    (hVsup : ⨆ μ, V μ = ⊤)
    (hstab : ∀ μ : Ω, ∀ l ∈ L, l • μ = μ → ∃ k : ℕ, ∀ v ∈ V μ, (l ^ 2 ^ k) • v = v)
    (ω₀ : Ω) {X : AddSubgroup M} (hXK : X ≤ commL M L) (hXne : X ≠ commL M L)
    (hXL : ∀ l ∈ L, ∀ x ∈ X, l • x ∈ X) :
    ∃ c ∈ commL M L, c ∉ X ∧ ∀ l ∈ L, l • ω₀ = ω₀ → l • c - c ∈ X := by
  classical
  by_contra hcon
  have hstar : ∀ c ∈ commL M L, (∀ l ∈ L, l • ω₀ = ω₀ → l • c - c ∈ X) → c ∈ X := by
    intro c hcK hcfix
    by_contra hcX
    exact hcon ⟨c, hcK, hcX, hcfix⟩
  have h5a : V ω₀ ⊓ commL M L ≤ X := by
    by_contra hnot
    let S : Subgroup H := L ⊓ MulAction.stabilizer H ω₀
    have hS : ∀ g : S, (g : H) ∈ L ∧ (g : H) • ω₀ = ω₀ := fun g =>
      ⟨(Subgroup.mem_inf.1 g.2).1, MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 g.2).2⟩
    have hZ : ∀ g : S, ∀ z ∈ V ω₀ ⊓ commL M L, g • z ∈ V ω₀ ⊓ commL M L := by
      intro g z hz
      obtain ⟨hgL, hgω⟩ := hS g
      refine AddSubgroup.mem_inf.2 ⟨?_, smul_mem_commL
        (fun l hl => L.mul_mem (L.mul_mem hgL hl) (L.inv_mem hgL)) (AddSubgroup.mem_inf.1 hz).2⟩
      have := hV g hgL ω₀ z (AddSubgroup.mem_inf.1 hz).1
      rw [hgω] at this
      exact this
    have hG : ∀ g : S, ∃ k : ℕ, ∀ z ∈ V ω₀ ⊓ commL M L, (g ^ 2 ^ k) • z - z ∈ X := by
      intro g
      obtain ⟨hgL, hgω⟩ := hS g
      obtain ⟨k, hk⟩ := hstab ω₀ g hgL hgω
      refine ⟨k, fun z hz => ?_⟩
      rw [show (g ^ 2 ^ k) • z = z from hk z (AddSubgroup.mem_inf.1 hz).1, sub_self]
      exact X.zero_mem
    obtain ⟨c, hcZ, hcX, hc⟩ := exists_fixed_mod_of_pow (G := S) h2 hZ
      (fun g x hx => hXL g (hS g).1 x hx) hG hnot
    exact hcX (hstar c (AddSubgroup.mem_inf.1 hcZ).2 fun l hl hlω =>
      hc ⟨l, Subgroup.mem_inf.2 ⟨hl, MulAction.mem_stabilizer_iff.2 hlω⟩⟩)
  have h5b : ∀ v ∈ V ω₀, ∀ l ∈ L, l • ω₀ = ω₀ → l • v - v ∈ X := by
    intro v hv l hl hlω
    refine h5a (AddSubgroup.mem_inf.2 ⟨sub_mem ?_ hv, sub_mem_commL hl v⟩)
    have := hV l hl ω₀ v hv
    rwa [hlω] at this
  choose s hsL hsω using fun μ : Ω => htrans ω₀ μ
  letI : Fintype Ω := Fintype.ofFinite Ω
  have hodd' : Fintype.card Ω % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]; exact Nat.odd_iff.mp hodd
  obtain ⟨Av, hAv⟩ : ∃ Av : M → M, ∀ v, Av v = ∑ μ, s μ • v := ⟨_, fun _ => rfl⟩
  have hAv1 : ∀ v : M, Av v - v ∈ commL M L := by
    intro v
    have h1 : Av v - v = ∑ μ, (s μ • v - v) := by
      rw [hAv, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        odd_nsmul_eq h2 hodd']
    rw [h1]
    exact sum_mem fun μ _ => sub_mem_commL (hsL μ) v
  have hAv2 : ∀ v ∈ V ω₀, ∀ g ∈ L, g • Av v - Av v ∈ X := by
    intro v hv g hg
    have h1 : ∑ μ, s μ • v = ∑ μ, s (g • μ) • v :=
      (Equiv.sum_comp (MulAction.toPerm g) (fun ν => s ν • v)).symm
    have h3 : g • Av v - Av v = ∑ μ, (g • (s μ • v) - s (g • μ) • v) := by
      rw [hAv, Finset.smul_sum, Finset.sum_sub_distrib, ← h1]
    rw [h3]
    refine sum_mem fun μ _ => ?_
    have hh : (s (g • μ))⁻¹ * g * s μ ∈ L :=
      L.mul_mem (L.mul_mem (L.inv_mem (hsL _)) hg) (hsL μ)
    have hhω : ((s (g • μ))⁻¹ * g * s μ) • ω₀ = ω₀ := by
      rw [mul_smul, mul_smul, hsω μ, inv_smul_eq_iff]
      exact (hsω (g • μ)).symm
    have e : g • (s μ • v) - s (g • μ) • v =
        s (g • μ) • (((s (g • μ))⁻¹ * g * s μ) • v - v) := by
      simp [smul_sub, smul_smul, mul_assoc]
    rw [e]
    exact hXL _ (hsL _) _ (h5b v hv _ hh hhω)
  have h5c : ∀ v ∈ V ω₀, ∀ g ∈ L, g • v - v ∈ X := by
    intro v hv g hg
    have hc : Av v - v ∈ X := by
      refine hstar _ (hAv1 v) fun l hl hlω => ?_
      have : l • (Av v - v) - (Av v - v) = (l • Av v - Av v) - (l • v - v) := by
        rw [smul_sub]; abel
      rw [this]
      exact sub_mem (hAv2 v hv l hl) (h5b v hv l hl hlω)
    have : g • v - v = (g • Av v - Av v) - (g • (Av v - v) - (Av v - v)) := by
      rw [smul_sub]; abel
    rw [this]
    exact sub_mem (hAv2 v hv g hg) (sub_mem (hXL g hg _ hc) hc)
  have h5d : ∀ μ : Ω, ∀ w ∈ V μ, ∀ g ∈ L, g • w - w ∈ X := by
    intro μ w hw g hg
    have hv : (s μ)⁻¹ • w ∈ V ω₀ := by
      have := hV (s μ)⁻¹ (L.inv_mem (hsL μ)) μ w hw
      have e : (s μ)⁻¹ • μ = ω₀ := by rw [inv_smul_eq_iff]; exact (hsω μ).symm
      rwa [e] at this
    have e2 : g • w - w = ((g * s μ) • ((s μ)⁻¹ • w) - (s μ)⁻¹ • w) -
        (s μ • ((s μ)⁻¹ • w) - (s μ)⁻¹ • w) := by
      rw [mul_smul, smul_inv_smul]; abel
    rw [e2]
    exact sub_mem (h5c _ hv _ (L.mul_mem hg (hsL μ))) (h5c _ hv _ (hsL μ))
  have hKX : commL M L ≤ X := by
    let T : AddSubgroup M :=
      { carrier := {m | ∀ g ∈ L, g • m - m ∈ X}
        add_mem' := fun {a b} ha hb g hg => by
          have : g • (a + b) - (a + b) = (g • a - a) + (g • b - b) := by rw [smul_add]; abel
          rw [this]; exact add_mem (ha g hg) (hb g hg)
        zero_mem' := fun g hg => by simp
        neg_mem' := fun {a} ha g hg => by
          have : g • (-a) - -a = -(g • a - a) := by rw [smul_neg]; abel
          rw [this]; exact neg_mem (ha g hg) }
    have hT : (⊤ : AddSubgroup M) ≤ T := by
      rw [← hVsup]
      exact iSup_le fun μ w hw g hg => h5d μ w hw g hg
    refine (AddSubgroup.closure_le X).2 ?_
    rintro _ ⟨l, hl, m, rfl⟩
    exact hT (AddSubgroup.mem_top m) l hl
  exact hXne (le_antisymm hXK hKX)

theorem exists_mul_pow_eq {L P : Subgroup H} (hPL : P ≤ Subgroup.normalizer (L : Set H))
    {a b : H} (ha : a ∈ L) (hb : b ∈ P) (n : ℕ) : ∃ a' ∈ L, (a * b) ^ n = a' * b ^ n := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨a', ha', h⟩ := ih
    refine ⟨a' * (b ^ n * a * (b ^ n)⁻¹), L.mul_mem ha'
      ((Subgroup.mem_normalizer_iff.mp (hPL (P.pow_mem hb n)) a).mp ha), ?_⟩
    rw [pow_succ (a * b), h, pow_succ b]
    simp only [mul_assoc, inv_mul_cancel_left]

theorem exists_avg_of_isPGroup [Finite Ω] [Finite M] (h2 : ∀ m : M, m + m = 0) {L : Subgroup H}
    (hLodd : L ≤ Subgroup.closure {h : H | h ∈ L ∧ Odd (orderOf h)})
    (htrans : ∀ μ ν : Ω, ∃ l ∈ L, l • μ = ν) (hodd : Odd (Nat.card Ω))
    (V : Ω → AddSubgroup M) (hV : ∀ l ∈ L, ∀ μ : Ω, ∀ v ∈ V μ, l • v ∈ V (l • μ))
    (hVsup : ⨆ μ, V μ = ⊤)
    (hstab : ∀ μ : Ω, ∀ l ∈ L, l • μ = μ → ∃ k : ℕ, ∀ v ∈ V μ, (l ^ 2 ^ k) • v = v)
    {P : Subgroup H} (hP : IsPGroup 2 P) (hPL : P ≤ Subgroup.normalizer (L : Set H))
    (hK : commL M L ≠ ⊥) (ω₀ : Ω) :
    ∃ (X : AddSubgroup M) (c : M),
      (∀ l ∈ L, ∀ x ∈ X, l • x ∈ X) ∧ (∀ p ∈ P, ∀ x ∈ X, p • x ∈ X) ∧
      c ∈ commL M L ∧ c ∉ X ∧
      (∀ l ∈ L, l • ω₀ = ω₀ → l • c - c ∈ X) ∧
      (∀ p ∈ P, ∀ l ∈ L, l • ω₀ = p • ω₀ → p • c - l • c ∈ X) ∧
      (∀ y ∈ commL M L, (∀ l ∈ L, l • y - y ∈ X) → y ∈ X) := by
  classical
  haveI : Finite (AddSubgroup M) :=
    Finite.of_injective (SetLike.coe : AddSubgroup M → Set M) SetLike.coe_injective
  obtain ⟨X, hXs, hXmax⟩ := Set.Finite.exists_maximal
    (s := {Y : AddSubgroup M | Y ≤ commL M L ∧ Y ≠ commL M L ∧
      (∀ l ∈ L, ∀ y ∈ Y, l • y ∈ Y) ∧ ∀ p ∈ P, ∀ y ∈ Y, p • y ∈ Y}) (Set.toFinite _)
    ⟨⊥, bot_le, fun h => hK h.symm,
      fun l _ y hy => by rw [(AddSubgroup.mem_bot).1 hy, smul_zero]; exact zero_mem _,
      fun p _ y hy => by rw [(AddSubgroup.mem_bot).1 hy, smul_zero]; exact zero_mem _⟩
  obtain ⟨hXK, hXne, hXL, hXP⟩ := hXs
  have hlast : ∀ y ∈ commL M L, (∀ l ∈ L, l • y - y ∈ X) → y ∈ X :=
    fun y hyK hy => mem_of_forall_smul_sub_mem h2 hLodd hPL hXK hXne hXL hXP
      (fun Y h1 h2 h3 h4 h5 => hXmax ⟨h1, h2, h3, h4⟩ h5) hyK hy
  obtain ⟨c₀, hc₀K, hc₀X, hc₀fix⟩ :=
    exists_commL_fixed h2 htrans hodd V hV hVsup hstab ω₀ hXK hXne hXL
  let C : AddSubgroup M :=
    { carrier := {c | c ∈ commL M L ∧ ∀ l ∈ L, l • ω₀ = ω₀ → l • c - c ∈ X}
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun l hl hlω => by
        have : l • (a + b) - (a + b) = (l • a - a) + (l • b - b) := by rw [smul_add]; abel
        rw [this]; exact add_mem (ha.2 l hl hlω) (hb.2 l hl hlω)⟩
      zero_mem' := ⟨zero_mem _, fun l hl _ => by simp⟩
      neg_mem' := fun {a} ha => ⟨neg_mem ha.1, fun l hl hlω => by
        have : l • (-a) - -a = -(l • a - a) := by rw [smul_neg]; abel
        rw [this]; exact neg_mem (ha.2 l hl hlω)⟩ }
  have hc₀C : c₀ ∈ C := ⟨hc₀K, hc₀fix⟩
  let Q : Subgroup H := (L ⊔ P) ⊓ MulAction.stabilizer H ω₀
  have hQ : ∀ g : Q, ∃ a ∈ L, ∃ b ∈ P, (g : H) = a * b := fun g => by
    have h : (g : H) ∈ ((L ⊔ P : Subgroup H) : Set H) := (Subgroup.mem_inf.1 g.2).1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L P hPL] at h
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 h
    exact ⟨a, ha, b, hb, hab.symm⟩
  have hQω : ∀ g : Q, (g : H) • ω₀ = ω₀ := fun g =>
    MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 g.2).2
  have hQX : ∀ g : Q, ∀ x ∈ X, g • x ∈ X := by
    intro g x hx
    obtain ⟨a, ha, b, hb, h⟩ := hQ g
    show (g : H) • x ∈ X
    rw [h, mul_smul]
    exact hXL a ha _ (hXP b hb x hx)
  have hQL : ∀ g : Q, ∀ l ∈ L, (g : H) * l * (g : H)⁻¹ ∈ L := by
    intro g l hl
    obtain ⟨a, ha, b, hb, h⟩ := hQ g
    have h1 : b * l * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hPL hb) l).mp hl
    rw [h, show a * b * l * (a * b)⁻¹ = a * (b * l * b⁻¹) * a⁻¹ by group]
    exact L.mul_mem (L.mul_mem ha h1) (L.inv_mem ha)
  have hQC : ∀ g : Q, ∀ c ∈ C, g • c ∈ C := by
    intro g c hc
    refine ⟨smul_mem_commL (hQL g) hc.1, fun l hl hlω => ?_⟩
    have hgl : (g : H)⁻¹ * l * g ∈ L := by
      have h := hQL g⁻¹ l hl
      rwa [Subgroup.coe_inv, inv_inv] at h
    have hglω : ((g : H)⁻¹ * l * g) • ω₀ = ω₀ := by
      rw [mul_smul, mul_smul, hQω g, hlω, inv_smul_eq_iff, hQω g]
    have : l • ((g : H) • c) - (g : H) • c = (g : H) • (((g : H)⁻¹ * l * g) • c - c) := by
      simp [smul_sub, smul_smul, mul_assoc]
    show l • ((g : H) • c) - (g : H) • c ∈ X
    rw [this]
    exact hQX g _ (hc.2 _ hgl hglω)
  have hG : ∀ g : Q, ∃ k : ℕ, ∀ c ∈ C, (g ^ 2 ^ k) • c - c ∈ X := by
    intro g
    obtain ⟨a, ha, b, hb, h⟩ := hQ g
    obtain ⟨k, hk⟩ := hP ⟨b, hb⟩
    have hbk : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨a', ha', hpow⟩ := exists_mul_pow_eq hPL ha hb (2 ^ k)
    have hg' : ((g ^ 2 ^ k : Q) : H) = a' := by
      rw [Subgroup.coe_pow, h, hpow, hbk, mul_one]
    have hω' : a' • ω₀ = ω₀ := by
      rw [← hg']
      exact MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 (g ^ 2 ^ k).2).2
    refine ⟨k, fun c hc => ?_⟩
    show ((g ^ 2 ^ k : Q) : H) • c - c ∈ X
    rw [hg']
    exact hc.2 a' ha' hω'
  obtain ⟨c, hcC, hcX, hc⟩ := exists_fixed_mod_of_pow (G := Q) h2 hQC hQX hG
    fun h => hc₀X (h hc₀C)
  refine ⟨X, c, hXL, hXP, hcC.1, hcX, hcC.2, fun p hp l hl hlω => ?_, hlast⟩
  have hg : l⁻¹ * p ∈ Q := Subgroup.mem_inf.2
    ⟨(L ⊔ P).mul_mem (Subgroup.mem_sup_left (L.inv_mem hl)) (Subgroup.mem_sup_right hp),
      MulAction.mem_stabilizer_iff.2 (by rw [mul_smul, ← hlω, inv_smul_smul])⟩
  have h1 : (l⁻¹ * p) • c - c ∈ X := hc ⟨_, hg⟩
  have : p • c - l • c = l • ((l⁻¹ * p) • c - c) := by simp [smul_sub, smul_smul]
  rw [this]
  exact hXL l hl _ h1

theorem exists_avg [Finite Ω] [Finite M] (h2 : ∀ m : M, m + m = 0) {L : Subgroup H}
    (hLodd : L ≤ Subgroup.closure {h : H | h ∈ L ∧ Odd (orderOf h)})
    (htrans : ∀ μ ν : Ω, ∃ l ∈ L, l • μ = ν) (hodd : Odd (Nat.card Ω))
    (V : Ω → AddSubgroup M) (hV : ∀ l ∈ L, ∀ μ : Ω, ∀ v ∈ V μ, l • v ∈ V (l • μ))
    (hVsup : ⨆ μ, V μ = ⊤)
    (hstab : ∀ μ : Ω, ∀ l ∈ L, l • μ = μ → ∃ k : ℕ, ∀ v ∈ V μ, (l ^ 2 ^ k) • v = v)
    {z : H} (hz : z * z = 1) (hzL : ∀ l ∈ L, z * l * z⁻¹ ∈ L) (hK : commL M L ≠ ⊥) (ω₀ : Ω) :
    ∃ (X : AddSubgroup M) (c : M),
      (∀ l ∈ L, ∀ x ∈ X, l • x ∈ X) ∧ (∀ x ∈ X, z • x ∈ X) ∧
      c ∈ commL M L ∧ c ∉ X ∧
      (∀ l ∈ L, l • ω₀ = ω₀ → l • c - c ∈ X) ∧
      (∀ l ∈ L, l • ω₀ = z • ω₀ → z • c - l • c ∈ X) ∧
      (∀ y ∈ commL M L, (∀ l ∈ L, l • y - y ∈ X) → y ∈ X) := by
  have hz1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hP : IsPGroup 2 (Subgroup.zpowers z) := by
    refine IsPGroup.iff_orderOf.2 fun g => ?_
    have h1 : orderOf g ∣ 2 ^ 1 := by
      rw [← Subgroup.orderOf_coe, pow_one]
      exact (orderOf_dvd_of_mem_zpowers g.2).trans
        (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hz))
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    exact ⟨m, hm⟩
  have hPL : Subgroup.zpowers z ≤ Subgroup.normalizer (L : Set H) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨hzL h, fun hh => ?_⟩
    have e : z * (z * h * z⁻¹) * z⁻¹ = h := by
      calc z * (z * h * z⁻¹) * z⁻¹ = z⁻¹ * (z * h * z⁻¹) * z := by rw [hz1]
        _ = h := by group
    rw [← e]
    exact hzL _ hh
  obtain ⟨X, c, hXL, hXP, hcK, hcX, hcfix, hcp, hlast⟩ :=
    exists_avg_of_isPGroup h2 hLodd htrans hodd V hV hVsup hstab hP hPL hK ω₀
  exact ⟨X, c, hXL, hXP z (Subgroup.mem_zpowers z), hcK, hcX, hcfix,
    hcp z (Subgroup.mem_zpowers z), hlast⟩

end CFSG.Quasithin.F112Crit.PermBound

end
