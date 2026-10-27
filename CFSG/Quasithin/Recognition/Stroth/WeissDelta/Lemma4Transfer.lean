module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.ClosedGoodPath

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

private theorem ClosedGoodPath.window_apply_zero (W : ClosedGoodPath H Γ) (s : ℕ) {j : ℕ}
    (hj : j ≤ s) : W.window 0 s j = W.x (j : ℤ) := by
  rw [ClosedGoodPath.window_apply W 0 (s := s) hj]
  congr 1
  omega

private theorem ClosedGoodPath.adj_nat (W : ClosedGoodPath H Γ) (j : ℕ) :
    Γ.Adj (W.x (j : ℤ)) (W.x ((j + 1 : ℕ) : ℤ)) := by
  simpa using W.adj (j : ℤ)

private theorem ClosedGoodPath.ne_add_two_nat (W : ClosedGoodPath H Γ) (j : ℕ) :
    W.x (j : ℤ) ≠ W.x ((j + 2 : ℕ) : ℤ) := by
  have h := W.ne_add_two (j : ℤ)
  rwa [show (j : ℤ) + 2 = ((j + 2 : ℕ) : ℤ) by omega] at h

theorem forall_smul_smul_eq_iff_commute {n : ℕ} (hn : 3 ≤ n) (hW : WeissFree H Γ n)
    {p : GPath Γ n} (hp : p.NoBack) {K : Subgroup H} (hKp : K ≤ GPath.stabPath (H := H) p)
    {b : V} (hb : Γ.Adj (p n) b) (hb1 : b ≠ p (n - 1)) (hKb : ∀ g ∈ K, g • b = b) {u : H}
    (hu : u ∈ pathRootGroup H Γ p) :
    (∀ g ∈ K, g • u • b = u • b) ↔ ∀ g ∈ K, g * u = u * g := by
  constructor
  · intro hfix g hgK
    have hgstab : g ∈ GPath.stabPath (H := H) p := hKp hgK
    have hgp : g • p = p := by
      rw [GPath.smul_eq_iff]
      intro i hi
      exact hgstab i hi
    have hginv : g⁻¹ • b = b := by
      have h := congrArg (fun w => g⁻¹ • w) (hKb g hgK)
      simpa using h.symm
    have hnorm : u⁻¹ * (g * u * g⁻¹) ∈ pathRootGroup H Γ p := by
      have hconj : g * u * g⁻¹ ∈ pathRootGroup H Γ p := by
        have hm : (MulAut.conj g) u ∈
            (pathRootGroup H Γ p).map (MulAut.conj g).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hu
        rwa [← pathRootGroup_smul_eq p g, hgp] at hm
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hconj
    have hfixb : (u⁻¹ * (g * u * g⁻¹)) • b = b := by
      calc
        (u⁻¹ * (g * u * g⁻¹)) • b = u⁻¹ • ((g * u * g⁻¹) • b) := by rw [mul_smul]
        _ = u⁻¹ • (g • (u • (g⁻¹ • b))) := by rw [mul_smul, mul_smul]
        _ = u⁻¹ • (g • (u • b)) := by rw [hginv]
        _ = u⁻¹ • (u • b) := by rw [hfix g hgK]
        _ = b := by rw [← mul_smul, inv_mul_cancel, one_smul]
    have hone : u⁻¹ * (g * u * g⁻¹) = 1 :=
      pathRootGroup_eq_one_of_fix_of_weissFree hn hW hp hnorm hb hb1 hfixb
    calc
      g * u = (g * u * g⁻¹) * g := by group
      _ = u * g := by
        have h : g * u * g⁻¹ = u := by
          have h' := congrArg (fun x : H => u * x) hone
          simpa [mul_assoc] using h'
        rw [h]
  · intro hcomm g hgK
    calc
      g • (u • b) = (g * u) • b := (mul_smul g u b).symm
      _ = (u * g) • b := by rw [hcomm g hgK]
      _ = u • (g • b) := mul_smul u g b
      _ = u • b := by rw [hKb g hgK]

theorem exists_fix_iff_of_noBack {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n) {p : GPath Γ n} (hp : p.NoBack)
    {K : Subgroup H} (hKp : K ≤ GPath.stabPath (H := H) p) {a b : V} (ha : Γ.Adj (p 0) a)
    (ha1 : a ≠ p 1) (hb : Γ.Adj (p n) b) (hb1 : b ≠ p (n - 1)) (hKa : ∀ g ∈ K, g • a = a)
    (hKb : ∀ g ∈ K, g • b = b) :
    (∃ z, Γ.Adj (p 0) z ∧ z ≠ p 1 ∧ z ≠ a ∧ ∀ g ∈ K, g • z = z) ↔
      ∃ z, Γ.Adj (p n) z ∧ z ≠ p (n - 1) ∧ z ≠ b ∧ ∀ g ∈ K, g • z = z := by
  have key : ∀ {q : GPath Γ n} {a b : V}, q.NoBack → K ≤ GPath.stabPath (H := H) q →
      Γ.Adj (q 0) a → a ≠ q 1 → (∀ g ∈ K, g • a = a) →
      Γ.Adj (q n) b → b ≠ q (n - 1) → (∀ g ∈ K, g • b = b) →
      (∃ z, Γ.Adj (q 0) z ∧ z ≠ q 1 ∧ z ≠ a ∧ ∀ g ∈ K, g • z = z) →
      ∃ z, Γ.Adj (q n) z ∧ z ≠ q (n - 1) ∧ z ≠ b ∧ ∀ g ∈ K, g • z = z := by
    intro q a b hq hKq haq ha1q hKaq hbq hb1q hKbq hthird
    obtain ⟨z, hzadj, hz1, hza, hzfix⟩ := hthird
    have hlast : q.rev n = q 0 := by
      rw [GPath.rev_apply _ le_rfl, Nat.sub_self]
    have hlastprev : q.rev (n - 1) = q 1 := by
      rw [GPath.rev_apply _ (by omega)]
      congr 1
      omega
    have hrevnb : q.rev.NoBack := hq.rev
    have hrevadj_a : Γ.Adj (q.rev n) a := by rw [hlast]; exact haq
    have hrevadj_z : Γ.Adj (q.rev n) z := by rw [hlast]; exact hzadj
    have hrevne_a : a ≠ q.rev (n - 1) := by rw [hlastprev]; exact ha1q
    have hrevne_z : z ≠ q.rev (n - 1) := by rw [hlastprev]; exact hz1
    obtain ⟨u, hua, -⟩ := pathRootGroup_regular_of_weissFree hn hM hW hrevnb
      hrevadj_a hrevadj_z hrevne_a hrevne_z
    let uH : H := u
    have hmemrev : uH ∈ pathRootGroup H Γ q.rev := u.2
    have huaH : uH • a = z := hua
    have hu : uH ∈ pathRootGroup H Γ q := by
      have h := hmemrev
      rw [pathRootGroup_rev_eq q] at h
      exact h
    have hu1 : uH ≠ 1 := by
      intro hone
      exact hza (by rw [← huaH, hone, one_smul])
    have hKqrev : K ≤ GPath.stabPath (H := H) q.rev := by
      rw [GPath.stabPath_rev q]
      exact hKq
    have hcore := forall_smul_smul_eq_iff_commute (K := K) hn hW hrevnb hKqrev
      (b := a) hrevadj_a hrevne_a hKaq (u := uH) hmemrev
    have hcomm : ∀ g ∈ K, g * uH = uH * g := hcore.mp (by
      intro g hgK
      rw [huaH]
      exact hzfix g hgK)
    have hpu : uH • q n = q n :=
      smul_path_eq_self_of_mem_pathRootGroup hn hu n le_rfl
    refine ⟨uH • b, ?_, ?_, ?_, ?_⟩
    · have hadj := (GraphAction.adj_smul uH (q n) b).mpr hbq
      rwa [hpu] at hadj
    · intro heq
      have hprev : uH • q (n - 1) = q (n - 1) :=
        smul_path_eq_self_of_mem_pathRootGroup hn hu (n - 1) (by omega)
      apply hb1q
      calc
        b = uH⁻¹ • (uH • b) := (inv_smul_smul uH b).symm
        _ = uH⁻¹ • q (n - 1) := by rw [heq]
        _ = q (n - 1) := by
          have h := congrArg (fun x => uH⁻¹ • x) hprev
          simpa using h.symm
    · intro heq
      exact hu1 (pathRootGroup_eq_one_of_fix_of_weissFree hn hW hq hu hbq hb1q heq)
    · intro g hgK
      calc
        g • (uH • b) = (g * uH) • b := (mul_smul g uH b).symm
        _ = (uH * g) • b := by rw [hcomm g hgK]
        _ = uH • (g • b) := mul_smul uH g b
        _ = uH • b := by rw [hKbq g hgK]
  constructor
  · intro hthird
    exact key (q := p) (a := a) (b := b) hp hKp ha ha1 hKa hb hb1 hKb hthird
  · intro hthird
    have hprev : (p.rev).NoBack := hp.rev
    have hKprev : K ≤ GPath.stabPath (H := H) p.rev := by
      rw [GPath.stabPath_rev p]
      exact hKp
    have hrev0 : p.rev 0 = p n := by
      rw [GPath.rev_apply _ (Nat.zero_le n), Nat.sub_zero]
    have hrev1 : p.rev 1 = p (n - 1) := by
      rw [GPath.rev_apply _ (by omega : 1 ≤ n)]
    have hrevn : p.rev n = p 0 := by
      rw [GPath.rev_apply _ le_rfl, Nat.sub_self]
    have hrevnm1 : p.rev (n - 1) = p 1 := by
      rw [GPath.rev_apply _ (by omega)]
      congr 1
      omega
    have hthird' : ∃ z, Γ.Adj (p.rev 0) z ∧ z ≠ p.rev 1 ∧ z ≠ b ∧
        ∀ g ∈ K, g • z = z := by
      obtain ⟨z, hzadj, hz1, hz2, hzfix⟩ := hthird
      exact ⟨z, by rwa [hrev0], by rwa [hrev1], hz2, hzfix⟩
    have hres := key (q := p.rev) (a := b) (b := a) hprev hKprev
      (by rw [hrev0]; exact hb) (by rw [hrev1]; exact hb1) hKb
      (by rw [hrevn]; exact ha) (by rw [hrevnm1]; exact ha1) hKa hthird'
    obtain ⟨z, hzadj, hz1, hza, hzfix⟩ := hres
    refine ⟨z, ?_, ?_, ?_, hzfix⟩
    · rwa [hrevn] at hzadj
    · rwa [hrevnm1] at hz1
    · exact hza

theorem ClosedGoodPath.hasThirdFix_add_iff [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (W : ClosedGoodPath H Γ) {K : Subgroup H} (hKW : K ≤ W.stab) (i : ℤ) :
    W.HasThirdFix K i ↔ W.HasThirdFix K (i + n) := by
  let p : GPath Γ n := W.window i n
  have hp0 : p 0 = W.x i := by
    rw [ClosedGoodPath.window_apply W i (s := n) (Nat.zero_le n)]
    simp
  have hp1 : p 1 = W.x (i + 1) := by
    rw [ClosedGoodPath.window_apply W i (s := n) (by omega : 1 ≤ n)]
    norm_num
  have hpn : p n = W.x (i + (n : ℤ)) :=
    ClosedGoodPath.window_apply W i (s := n) le_rfl
  have hcastn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hidx1 : (i + (n : ℤ)) - 1 = i + ((n - 1 : ℕ) : ℤ) := by
    rw [hcastn1]
    ring
  have hpn1 : p (n - 1) = W.x (i + ((n - 1 : ℕ) : ℤ)) :=
    ClosedGoodPath.window_apply W i (s := n) (by omega)
  have hp : p.NoBack := by
    have hgood : IsGoodPath H p := W.good i n p fun j hj => by
      rw [ClosedGoodPath.window_apply W i (s := n) hj]
    exact hgood.1
  have hKp : K ≤ GPath.stabPath (H := H) p :=
    le_trans hKW (ClosedGoodPath.stab_le_stabPath_window W i n)
  have ha : Γ.Adj (p 0) (W.x (i - 1)) := by
    rw [hp0]
    have h := W.adj (i - 1)
    rw [show i - 1 + 1 = i by ring] at h
    exact h.symm
  have ha1 : W.x (i - 1) ≠ p 1 := by
    rw [hp1]
    have h := W.ne_add_two (i - 1)
    rwa [show i - 1 + 2 = i + 1 by ring] at h
  have hb : Γ.Adj (p n) (W.x (i + (n : ℤ) + 1)) := by
    rw [hpn]
    exact W.adj (i + (n : ℤ))
  have hb1 : W.x (i + (n : ℤ) + 1) ≠ p (n - 1) := by
    rw [hpn1, ← hidx1]
    have h := W.ne_add_two (i + (n : ℤ) - 1)
    rw [show i + (n : ℤ) - 1 + 2 = i + (n : ℤ) + 1 by ring] at h
    exact fun heq => h heq.symm
  have hKa : ∀ g ∈ K, g • W.x (i - 1) = W.x (i - 1) :=
    fun g hgK => (ClosedGoodPath.mem_stab_iff.mp (hKW hgK)) (i - 1)
  have hKb : ∀ g ∈ K, g • W.x (i + (n : ℤ) + 1) = W.x (i + (n : ℤ) + 1) :=
    fun g hgK => (ClosedGoodPath.mem_stab_iff.mp (hKW hgK)) (i + (n : ℤ) + 1)
  have hmain := exists_fix_iff_of_noBack hn hM hW hp hKp ha ha1 hb hb1 hKa hKb
  constructor
  · intro hthird
    unfold ClosedGoodPath.HasThirdFix at hthird
    obtain ⟨z, hzadj, hz1, hz2, hzfix⟩ := hthird
    have hfar := hmain.mp ⟨z, by rwa [hp0], by rwa [hp1], hz1, hzfix⟩
    obtain ⟨z', hz'adj, hz'1, hz'2, hz'fix⟩ := hfar
    refine ⟨z', ?_, ?_, ?_, hz'fix⟩
    · rw [hpn] at hz'adj
      exact hz'adj
    · rw [hpn1, ← hidx1] at hz'1
      exact hz'1
    · exact hz'2
  · intro hthird
    unfold ClosedGoodPath.HasThirdFix at hthird
    obtain ⟨z, hzadj, hz1, hz2, hzfix⟩ := hthird
    have hnear := hmain.mpr ⟨z, by rw [hpn]; exact hzadj,
      by rw [hpn1, ← hidx1]; exact hz1, hz2, hzfix⟩
    obtain ⟨z', hz'adj, hz'1, hz'2, hz'fix⟩ := hnear
    refine ⟨z', ?_, ?_, ?_, hz'fix⟩
    · rw [hp0] at hz'adj
      exact hz'adj
    · exact hz'2
    · rw [hp1] at hz'1
      exact hz'1

theorem ClosedGoodPath.exists_smul_eq [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w) (hL : ∀ z, LocalFacts H Γ z)
    (hloc : ∀ w u v : V, Γ.Adj w u → Γ.Adj w v → ∃ g : H, g • w = w ∧ g • u = v)
    (W W' : ClosedGoodPath H Γ) (h0 : ∃ g : H, g • W.x 0 = W'.x 0) :
    ∃ g : H, ∀ i, g • W.x i = W'.x i := by
  classical
  let p : GPath Γ (n + 1) := W'.window 0 (n + 1)
  have hp : p.NoBack := by
    have hgood : IsGoodPath H p := W'.good 0 (n + 1) p fun j hj => by
      rw [ClosedGoodPath.window_apply_zero W' (n + 1) hj]
      congr 1
      omega
    exact hgood.1
  have key : ∀ j : ℕ, j ≤ n + 1 → ∃ g : H, ∀ k : ℕ, k ≤ j → g • W.x k = W'.x k := by
    intro j
    induction j with
    | zero =>
      intro _
      obtain ⟨g, hg⟩ := h0
      refine ⟨g, fun k hk => ?_⟩
      have hk0 : k = 0 := by omega
      subst hk0
      exact hg
    | succ j ih =>
      intro hj
      obtain ⟨g, hg⟩ := ih (by omega)
      by_cases hj0 : j = 0
      · subst hj0
        have hadj : Γ.Adj (W'.x 0) (g • W.x 1) := by
          have h := (GraphAction.adj_smul g (W.x 0) (W.x 1)).mpr (W.adj 0)
          rw [show g • W.x 0 = W'.x 0 from hg 0 (by omega)] at h
          exact h
        have hadj' : Γ.Adj (W'.x 0) (W'.x 1) := W'.adj 0
        obtain ⟨h, hw, hu⟩ := hloc (W'.x 0) (g • W.x 1) (W'.x 1) hadj hadj'
        refine ⟨h * g, fun k hk => ?_⟩
        rcases (by omega : k = 0 ∨ k = 1) with hk0 | hk1
        · subst hk0
          rw [mul_smul, hg 0 (by omega)]
          simpa using hw
        · subst hk1
          rw [mul_smul]
          simpa using hu
      · have hjpos : 1 ≤ j := by omega
        have hjle : j ≤ n + 1 := by omega
        have hle : j ≤ n := by omega
        have hpj : p j = W'.x (j : ℤ) := ClosedGoodPath.window_apply_zero W' (n + 1) hjle
        have hpjm1 : p (j - 1) = W'.x ((j - 1 : ℕ) : ℤ) :=
          ClosedGoodPath.window_apply_zero W' (n + 1) (by omega)
        have hadj_u : Γ.Adj (p j) (g • W.x (j + 1)) := by
          rw [hpj]
          have h := (GraphAction.adj_smul g (W.x (j : ℤ))
            (W.x ((j + 1 : ℕ) : ℤ))).mpr (W.adj_nat j)
          rw [show g • W.x (j : ℤ) = W'.x (j : ℤ) from hg j (by omega)] at h
          exact h
        have hadj_v : Γ.Adj (p j) (W'.x (j + 1 : ℕ)) := by
          rw [hpj]
          exact W'.adj_nat j
        have hune : g • W.x (j + 1 : ℕ) ≠ p (j - 1) := by
          rw [hpjm1]
          intro heq
          have hinj : W.x ((j + 1 : ℕ) : ℤ) = W.x ((j - 1 : ℕ) : ℤ) := by
            have h2 : g • W.x ((j + 1 : ℕ) : ℤ) = g • W.x ((j - 1 : ℕ) : ℤ) :=
              heq.trans (hg (j - 1) (by omega)).symm
            have h := congrArg (fun v => g⁻¹ • v) h2
            simpa using h
          have h := W.ne_add_two_nat (j - 1)
          rw [show j - 1 + 2 = j + 1 by omega] at h
          exact h hinj.symm
        have hvne : W'.x (j + 1 : ℕ) ≠ p (j - 1) := by
          rw [hpjm1]
          intro heq
          have h := W'.ne_add_two_nat (j - 1)
          rw [show j - 1 + 2 = j + 1 by omega] at h
          exact h heq.symm
        obtain ⟨h, hhmem, hhu⟩ := exists_smul_of_mem_stabPath_take (n := n)
          (s := n + 1) (p := p) hn hM hne hp hjpos hjle hle hadj_u hadj_v hune hvne
        have hfix : ∀ k : ℕ, k ≤ j → h • W'.x k = W'.x k := by
          intro k hk
          have hk' := (GPath.mem_stabPath_iff.mp hhmem) k hk
          rw [GPath.take_apply_of_le p j hjle hk,
            ClosedGoodPath.window_apply_zero W' (n + 1) (by omega : k ≤ n + 1)] at hk'
          exact hk'
        refine ⟨h * g, fun k hk => ?_⟩
        by_cases hkj : k ≤ j
        · rw [mul_smul, hg k hkj, hfix k hkj]
        · have hk' : k = j + 1 := by omega
          subst hk'
          rw [mul_smul]
          simpa [Nat.cast_add, Nat.cast_one] using hhu
  obtain ⟨g, hg⟩ := key (n + 1) le_rfl
  refine ⟨g, fun i => ?_⟩
  have hwin : ∀ j : ℕ, j ≤ n + 1 → (W.smul g).x (0 + j) = W'.x (0 + j) := by
    intro j hj
    rw [ClosedGoodPath.smul_x, zero_add]
    exact hg j hj
  have hx := ClosedGoodPath.x_eq_of_window hn hW hL (W.smul g) W' 0 hwin
  simpa only [ClosedGoodPath.smul_x] using hx i

theorem ClosedGoodPath.not_hasThirdFix_of_mem [Finite V] [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w) (hL : ∀ z, LocalFacts H Γ z)
    (hloc : ∀ w u v : V, Γ.Adj w u → Γ.Adj w v → ∃ g : H, g • w = w ∧ g • u = v)
    {p : GPath Γ (n + 1)} (hp : p.NoBack) {i : ℕ} (hi0 : 0 < i) (hin : i < n) {g : H}
    (hg : g ∈ fixingSubgroup H (Γ.neighborSet (p 0)) ⊓ GPath.stabPath (H := H) p)
    (hfix : ∀ z, Γ.Adj (p i) z → z ≠ p (i - 1) → z ≠ p (i + 1) → g • z ≠ z)
    (W : ClosedGoodPath H Γ) (hW0 : ∃ h : H, h • p 0 = W.x 0) :
    ¬ W.HasThirdFix (W.kernelAt 0) i := by
  obtain ⟨Wp, hWp⟩ := ClosedGoodPath.exists_of_noBack hn hM hW hne hL hp
  have hgstab : g ∈ Wp.stab := by
    rw [← ClosedGoodPath.stabPath_window hn hW hL Wp 0]
    rw [GPath.mem_stabPath_iff]
    intro j hj
    have h := (GPath.mem_stabPath_iff.mp hg.2) j (by omega)
    have h' : g • Wp.x (j : ℤ) = Wp.x (j : ℤ) := by
      rw [hWp j (by omega)]
      exact h
    rw [ClosedGoodPath.window_apply_zero Wp (n + 1) hj]
    exact h'
  have hgfix : g ∈ fixingSubgroup H (Γ.neighborSet (Wp.x 0)) := by
    rw [show Wp.x 0 = p 0 from hWp 0 (by omega)]
    exact hg.1
  have hgker : g ∈ Wp.kernelAt 0 := ⟨hgfix, hgstab⟩
  have h0 : ∃ h : H, h • Wp.x (0 : ℤ) = W.x (0 : ℤ) := by
    obtain ⟨h, hh⟩ := hW0
    refine ⟨h, ?_⟩
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num, hWp 0 (by omega)]
    exact hh
  obtain ⟨h, hh⟩ := ClosedGoodPath.exists_smul_eq hn hM hW hne hL hloc Wp W h0
  have hker := ClosedGoodPath.kernelAt_eq_map_conj Wp W hh 0
  intro hthird
  unfold ClosedGoodPath.HasThirdFix at hthird
  obtain ⟨z, hzadj, hz1, hz2, hzfix⟩ := hthird
  have hmap : (MulAut.conj h) g ∈ W.kernelAt 0 := by
    rw [hker]
    exact Subgroup.mem_map_of_mem _ hgker
  have hgz : g • (h⁻¹ • z) = h⁻¹ • z := by
    have h1 : ((MulAut.conj h) g) • z = z := hzfix _ hmap
    have h2 := congrArg (fun w => h⁻¹ • w) h1
    simpa [MulAut.conj_apply, mul_smul] using h2
  have hcast1 : ((i : ℤ) - 1) = ((i - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ i)]
    norm_num
  have hcast2 : ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  have hWxi : W.x (i : ℤ) = h • p i := by
    calc
      W.x (i : ℤ) = h • Wp.x (i : ℤ) := (hh (i : ℤ)).symm
      _ = h • p i := by rw [hWp i (by omega)]
  have hWxi1 : W.x ((i : ℤ) - 1) = h • p (i - 1) := by
    calc
      W.x ((i : ℤ) - 1) = h • Wp.x ((i : ℤ) - 1) := (hh ((i : ℤ) - 1)).symm
      _ = h • Wp.x ((i - 1 : ℕ) : ℤ) := by rw [hcast1]
      _ = h • p (i - 1) := by rw [hWp (i - 1) (by omega)]
  have hWxi2 : W.x ((i : ℤ) + 1) = h • p (i + 1) := by
    calc
      W.x ((i : ℤ) + 1) = h • Wp.x ((i : ℤ) + 1) := (hh ((i : ℤ) + 1)).symm
      _ = h • Wp.x ((i + 1 : ℕ) : ℤ) := by rw [hcast2]
      _ = h • p (i + 1) := by rw [hWp (i + 1) (by omega)]
  have hz'adj : Γ.Adj (p i) (h⁻¹ • z) := by
    have hadj := (GraphAction.adj_smul h⁻¹ (h • p i) z).mpr (by
      rw [← hWxi]
      exact hzadj)
    rw [inv_smul_smul] at hadj
    exact hadj
  have hz'1 : h⁻¹ • z ≠ p (i - 1) := by
    intro heq
    have hz : z = h • p (i - 1) := by
      calc
        z = h • (h⁻¹ • z) := (smul_inv_smul h z).symm
        _ = h • p (i - 1) := by rw [heq]
    rw [← hWxi1] at hz
    exact hz1 hz
  have hz'2 : h⁻¹ • z ≠ p (i + 1) := by
    intro heq
    have hz : z = h • p (i + 1) := by
      calc
        z = h • (h⁻¹ • z) := (smul_inv_smul h z).symm
        _ = h • p (i + 1) := by rw [heq]
    rw [← hWxi2] at hz
    exact hz2 hz
  exact (hfix (h⁻¹ • z) hz'adj hz'1 hz'2) hgz

end CFSG.Quasithin.Stroth.WeissDelta

end
