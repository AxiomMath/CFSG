module

public import CFSG.RankThree.GF2n.Tim77.Sec3Basic
public import CFSG.RankThree.GF2n.Tim77Prop24TwoD
public import CFSG.CGT.T75N.BenderCenter
public import CFSG.CGT.T75N.UnitaryTwoGen
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

theorem sec49_dihedral_swap {G : Type} [Group G] {a r : G} (ha : a * a = 1)
    (har : a * r * a = r⁻¹) {k : ℕ} (hk : r ^ (2 * k + 1) = 1) :
    (r ^ k * a) * a * (r ^ k * a)⁻¹ = a * r ∧
      (r ^ k * a) * (a * r) * (r ^ k * a)⁻¹ = a ∧
        (r ^ k * a) * (r ^ k * a) = 1 := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have h1 : (a * r * a⁻¹) ^ k = a * r ^ k * a⁻¹ := conj_pow
  rw [ha', har, inv_pow] at h1
  have h2 : a * (r ^ k)⁻¹ = r ^ k * a := by
    rw [h1]
    calc a * (a * r ^ k * a) = (a * a) * r ^ k * a := by group
      _ = r ^ k * a := by rw [ha, one_mul]
  have h3 : r ^ k * r ^ k = r⁻¹ := by
    have e : r ^ k * r ^ k * r = r ^ (2 * k + 1) := by
      rw [← pow_add, ← pow_succ]
      congr 1
      ring
    exact eq_inv_of_mul_eq_one_left (by rw [e, hk])
  have e1 : (r ^ k * a) * a * (r ^ k * a)⁻¹ = a * r := by
    calc (r ^ k * a) * a * (r ^ k * a)⁻¹ = r ^ k * (a * a) * (a * (r ^ k)⁻¹) := by
          rw [mul_inv_rev, ha']
          group
      _ = r ^ k * (a * (r ^ k)⁻¹) := by rw [ha, mul_one]
      _ = r ^ k * (r ^ k * a) := by rw [h2]
      _ = (r ^ k * r ^ k) * a := by group
      _ = r⁻¹ * a := by rw [h3]
      _ = a * r := by
          calc r⁻¹ * a = (a * r * a) * a := by rw [har]
            _ = a * r := by rw [mul_assoc (a * r) a a, ha, mul_one]
  have e2 : (r ^ k * a) * (a * r) * (r ^ k * a)⁻¹ = a := by
    have e : r ^ k * r * r ^ k = r ^ (2 * k + 1) := by
      rw [← pow_succ, ← pow_add]
      congr 1
      ring
    calc (r ^ k * a) * (a * r) * (r ^ k * a)⁻¹ = r ^ k * (a * a) * r * (a * (r ^ k)⁻¹) := by
          rw [mul_inv_rev, ha']
          group
      _ = r ^ k * r * (a * (r ^ k)⁻¹) := by rw [ha, mul_one]
      _ = r ^ k * r * (r ^ k * a) := by rw [h2]
      _ = (r ^ k * r * r ^ k) * a := by group
      _ = a := by rw [e, hk, one_mul]
  refine ⟨e1, e2, ?_⟩
  calc (r ^ k * a) * (r ^ k * a) = r ^ k * (a * r ^ k * a) := by group
    _ = r ^ k * (r ^ k)⁻¹ := by rw [← h1]
    _ = 1 := mul_inv_cancel _

theorem sec49_mem_normalizer_conj {G : Type} [Group G] (g x : G) (T : Subgroup G) :
    x ∈ Subgroup.normalizer (conjSubgroup g T : Set G) ↔
      g⁻¹ * x * g ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h z
    have hz := h (g * z * g⁻¹)
    have e1 : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    have e2 : g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g = (g⁻¹ * x * g) * z * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [mem_conjSubgroup, mem_conjSubgroup, e1, e2] at hz
    exact hz
  · intro h y
    have hy := h (g⁻¹ * y * g)
    have e3 : (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * y * x⁻¹) * g := by
      group
    rw [e3] at hy
    rw [mem_conjSubgroup, mem_conjSubgroup]
    exact hy

theorem sec49_conjSubgroup_mono {G : Type} [Group G] {g : G} {X Y : Subgroup G}
    (h : X ≤ Y) : conjSubgroup g X ≤ conjSubgroup g Y :=
  fun _ hx => mem_conjSubgroup.mpr (h (mem_conjSubgroup.mp hx))

theorem sec49_inv_mul_mem_index_two {G : Type} [Group G] {K A : Subgroup G}
    (h2 : K.relIndex A = 2) {a a' : G} (ha : a ∈ A) (ha' : a' ∈ A)
    (haK : a ∉ K) (ha'K : a' ∉ K) : a⁻¹ * a' ∈ K := by
  have hidx : (K.subgroupOf A).index = 2 := h2
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff'.mp hidx
  have key : ∀ b : A, b ∉ K.subgroupOf A → c * b ∈ K.subgroupOf A := by
    intro b hb
    rcases hc b with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 hb
  have hna : (⟨a, ha⟩ : A) ∉ K.subgroupOf A := by
    rw [Subgroup.mem_subgroupOf]
    exact haK
  have hna' : (⟨a', ha'⟩ : A) ∉ K.subgroupOf A := by
    rw [Subgroup.mem_subgroupOf]
    exact ha'K
  have hm := (K.subgroupOf A).mul_mem ((K.subgroupOf A).inv_mem (key _ hna))
    (key _ hna')
  rw [Subgroup.mem_subgroupOf] at hm
  have e : ((c : G) * a)⁻¹ * ((c : G) * a') = a⁻¹ * a' := by group
  simpa [Subgroup.coe_mul, Subgroup.coe_inv, e] using hm

theorem tim77Sec49_holds :
    Tim77Sec49Statement := by
  intro G _ _ A Abar S₀ B h hq hA0
  have hZ : Section3.A0 A Abar ≤ (Subgroup.center (Section5.H A Abar)).map
      (Section5.H A Abar).subtype := hA0
  have hCen : CFSG.CGT.Timmesfeld75.BenderCenterInput := CFSG.CGT.T75N.benderCenterInput
  have hU : CFSG.CGT.Timmesfeld75.UnitaryTwoGenerationInput :=
    CFSG.CGT.T75N.unitaryTwoGenerationInput
  have hS : Prop24Setup A Abar (Section3.A0 A Abar) (Section3.Abar0 A Abar)
      (Section3.M A Abar) := h.setup
  have hA0ne : Section3.A0 A Abar ≠ A := h.a0_ne
  have hA0bot : Section3.A0 A Abar ≠ ⊥ := h.a0_ne_bot
  have hAb0ne : Section3.Abar0 A Abar ≠ Abar := hS.Lb_ne
  have hidx : (Section3.A0 A Abar).relIndex A = 2 := by
    rw [← hS.relIndex_Lb]
    exact hq
  obtain ⟨a, ha, haA0⟩ : ∃ a ∈ A, a ∉ Section3.A0 A Abar :=
    SetLike.exists_of_lt (lt_of_le_of_ne hS.L_le hA0ne)
  obtain ⟨b, hb, hbA0⟩ : ∃ b ∈ Abar, b ∉ Section3.Abar0 A Abar :=
    SetLike.exists_of_lt (lt_of_le_of_ne hS.Lb_le hAb0ne)
  obtain ⟨g0, hg0⟩ := hS.conj
  have hsqA : ∀ x ∈ A, x * x = 1 := fun x hx => hS.sq_A hx
  have hsqAb : ∀ x ∈ Abar, x * x = 1 := fun x hx => hS.sq_Ab hx
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsqA a ha)
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsqAb b hb)
  obtain ⟨k, hk⟩ := hS.odd_orderOf_mul ha haA0 hb hbA0
  have hr : (a * b) ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one _
  have har : a * (a * b) * a = (a * b)⁻¹ := by
    rw [mul_inv_rev, hbinv, hainv]
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [hsqA a ha, one_mul]
  have hab : a * (a * b) = b := by rw [← mul_assoc, hsqA a ha, one_mul]
  obtain ⟨h1, h2, h3⟩ := sec49_dihedral_swap (hsqA a ha) har hr
  rw [hab] at h1 h2
  set w := (a * b) ^ k * a with hw
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right h3
  rw [hwinv] at h1 h2
  have hbw : b ∈ conjSubgroup w A := by
    rw [mem_conjSubgroup, hwinv, h2]
    exact ha
  have hbg0 : b ∈ conjSubgroup g0 A := by
    rw [← hg0]
    exact hb
  have hb1 : b ≠ 1 := fun e => hbA0 (by rw [e]; exact Subgroup.one_mem _)
  have hne : conjSubgroup w A ⊓ conjSubgroup g0 A ≠ ⊥ := by
    intro hbot
    have hm : b ∈ conjSubgroup w A ⊓ conjSubgroup g0 A := Subgroup.mem_inf.mpr ⟨hbw, hbg0⟩
    rw [hbot, Subgroup.mem_bot] at hm
    exact hb1 hm
  have hwA : conjSubgroup w A = Abar := by
    rw [hg0]
    exact conjSubgroup_eq_of_inf_ne_bot h.hyp.ti hne
  have hwAb : conjSubgroup w Abar = A := by
    rw [← hwA, ← conjSubgroup_mul, h3, conjSubgroup_one]
  have hNA : ∀ x : G, x ∈ normalizer (A : Set G) ↔
      w⁻¹ * x * w ∈ normalizer (Abar : Set G) := by
    intro x
    have hx := sec49_mem_normalizer_conj w x Abar
    rw [hwAb] at hx
    exact hx
  have hconjA0 : conjSubgroup w (Section3.A0 A Abar) = Section3.Abar0 A Abar := by
    ext x
    rw [mem_conjSubgroup, h.a0_eq, h.abar0_eq, Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨h1', h2'⟩
      refine ⟨?_, (hNA x).mpr h2'⟩
      rw [← hwA]
      exact mem_conjSubgroup.mpr h1'
    · rintro ⟨h1', h2'⟩
      refine ⟨?_, (hNA x).mp h2'⟩
      have hx : x ∈ conjSubgroup w A := by
        rw [hwA]
        exact h1'
      exact mem_conjSubgroup.mp hx
  have hHle : ∀ y ∈ Section3.Abar0 A Abar, y ∈ Section5.H A Abar := by
    intro y hy
    have hN : conjSubgroup w (Section3.A0 A Abar) ≤ normalizer (A : Set G) := by
      rw [hconjA0, h.abar0_eq]
      exact inf_le_right
    unfold Section5.H CFSG.Timmesfeld.RootInvolutions.weakClosure
    exact Subgroup.subset_closure ⟨w, hN, by rw [hconjA0]; exact hy⟩
  have hKey : ∀ x ∈ A, (∀ y ∈ Section5.H A Abar, x * y = y * x) → x ∈ Section3.A0 A Abar := by
    intro x hx hcomm
    by_contra hxA0
    obtain ⟨⟨l, hl⟩, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA0bot
    have hl1' : l ≠ 1 := fun e => hl1 (Subtype.ext e)
    obtain ⟨n, hn, hnl⟩ := hS.exists_commutator_eq hx hxA0 hl
    have hc : x * n = n * x := hcomm n (hHle n hn)
    have h4 : x * n * x⁻¹ * n⁻¹ = 1 := by
      rw [hc]
      group
    exact hl1' (hnl.symm.trans h4)
  have hHnorm : ∀ g ∈ normalizer (A : Set G), ∀ y ∈ Section5.H A Abar,
      g * y * g⁻¹ ∈ Section5.H A Abar := by
    intro g hg
    have key : Section5.H A Abar ≤
        (Section5.H A Abar).comap (MulAut.conj g).toMonoidHom := by
      unfold Section5.H CFSG.Timmesfeld.RootInvolutions.weakClosure
      rw [Subgroup.closure_le]
      rintro z ⟨k', hk', hzk⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      show g * z * g⁻¹ ∈ _
      refine Subgroup.subset_closure ⟨g * k', ?_, ?_⟩
      · intro u hu
        rw [conjSubgroup_mul, mem_conjSubgroup] at hu
        have hz := hk' hu
        have e : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hz) (Subgroup.inv_mem _ hg)
      · rw [mem_conjSubgroup]
        have e : (g * k')⁻¹ * (g * z * g⁻¹) * (g * k') = k'⁻¹ * z * k' := by group
        rw [e]
        exact mem_conjSubgroup.mp hzk
    intro y hy
    exact key hy
  have hA0norm : ∀ g ∈ normalizer (A : Set G), ∀ a ∈ Section3.A0 A Abar,
      g * a * g⁻¹ ∈ Section3.A0 A Abar := by
    intro g hg a ha
    have haA : a ∈ A := hS.L_le ha
    have hcen : ∀ y ∈ Section5.H A Abar, y * a = a * y := by
      intro y hy
      obtain ⟨z, hz, hza⟩ := Subgroup.mem_map.mp (hZ ha)
      have hz' := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
      have hzv : (z : G) = a := by simpa using hza
      simpa [hzv] using hz'
    apply hKey (g * a * g⁻¹) ((Subgroup.mem_normalizer_iff.mp hg a).mp haA)
    intro y hy
    have hy' := hHnorm g⁻¹ (Subgroup.inv_mem _ hg) y hy
    rw [inv_inv] at hy'
    have hc := hcen _ hy'
    calc g * a * g⁻¹ * y = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by rw [hc]
      _ = y * (g * a * g⁻¹) := by group
  have hTIA0 : IsTI (Section3.A0 A Abar) := by
    intro g
    by_cases hne : Section3.A0 A Abar ⊓ conjSubgroup g (Section3.A0 A Abar) = ⊥
    · exact Or.inl hne
    · right
      have hAne : A ⊓ conjSubgroup g A ≠ ⊥ := fun hbot =>
        hne (le_bot_iff.mp (le_trans (inf_le_inf hS.L_le (sec49_conjSubgroup_mono hS.L_le))
          hbot.le))
      have hgA : conjSubgroup g A = A := conjSubgroup_eq_of_isTI h.hyp.ti hAne
      have hgN : g ∈ normalizer (A : Set G) := conjSubgroup_eq_self_iff.mp hgA
      have hconj : conjSubgroup g (Section3.A0 A Abar) = Section3.A0 A Abar := by
        apply le_antisymm
        · intro x hx
          rw [mem_conjSubgroup] at hx
          have hx' := hA0norm g hgN _ hx
          rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at hx'
        · intro x hx
          rw [mem_conjSubgroup]
          have hx' := hA0norm g⁻¹ (Subgroup.inv_mem _ hgN) x hx
          rwa [inv_inv] at hx'
      rw [hconj, inf_idem]
  have hconj2 : ∀ a ∈ A, a ∉ Section3.A0 A Abar → ∀ a' ∈ A, a' ∉ Section3.A0 A Abar →
      ∃ n ∈ Section5.H A Abar, n * a * n⁻¹ = a' := by
    intro a1 ha1 ha1A0 a2 ha2 ha2A0
    have hc : a1⁻¹ * a2 ∈ Section3.A0 A Abar :=
      sec49_inv_mul_mem_index_two hidx ha1 ha2 ha1A0 ha2A0
    obtain ⟨n, hn, hnc⟩ := hS.exists_commutator_eq ha1 ha1A0 hc
    have hnAb : n ∈ Abar := hS.Lb_le hn
    have ha1i : a1⁻¹ = a1 := inv_eq_of_mul_eq_one_right (hsqA a1 ha1)
    have hni : n⁻¹ = n := inv_eq_of_mul_eq_one_right (hsqAb n hnAb)
    have hsq1 : a1⁻¹ * a1⁻¹ = 1 := by
      rw [← mul_inv_rev, hsqA a1 ha1, inv_one]
    have e : n * a1⁻¹ * n⁻¹ = a2 := by
      calc n * a1⁻¹ * n⁻¹ = a1⁻¹ * (a1 * n * a1⁻¹ * n⁻¹) := by group
        _ = a1⁻¹ * (a1⁻¹ * a2) := by rw [hnc]
        _ = (a1⁻¹ * a1⁻¹) * a2 := by group
        _ = a2 := by rw [hsq1, one_mul]
    refine ⟨n, hHle n hn, ?_⟩
    rw [ha1i, hni] at e
    rw [hni]
    exact e
  have hconj4 : ∀ x ∈ normalizer (A : Set G), x ≠ 1 → (∃ g : G, x ∈ conjSubgroup g A) →
      Section3.A0 A Abar = A ⊓ centralizer ({x} : Set G) ∨ x ∈ centralizer (A : Set G) := by
    intro x hxN hx1 hxg
    obtain ⟨g, hxg⟩ := hxg
    by_cases hcomm : ∀ c ∈ A, ∀ d ∈ conjSubgroup g A, c * d = d * c
    · right
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact hcomm c hc x hxg
    · left
      have hBel := isElemAbelian_conj h.hyp.elemAbelian g
      have hBti := isTI_conjSubgroup h.hyp.ti g
      have hAconj : A = conjSubgroup g⁻¹ (conjSubgroup g A) := by
        rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
      have hBN : ¬ conjSubgroup g A ≤ normalizer (A : Set G) := by
        intro hBle
        have hAB := tim77_2_3 (g := g) h.hyp.elemAbelian h.hyp.ti hBle
        exact hcomm fun c hc d hd => by
          have hcd := congrArg Subtype.val
            (hAB.1.is_comm.comm ⟨c, Subgroup.mem_sup_left hc⟩ ⟨d, Subgroup.mem_sup_right hd⟩)
          simpa using hcd
      have hS0 : Prop24Setup (conjSubgroup g A) A
          (conjSubgroup g A ⊓ normalizer (A : Set G))
          (A ⊓ normalizer (conjSubgroup g A : Set G))
          ((conjSubgroup g A ⊓ normalizer (A : Set G)) ⊔
            (A ⊓ normalizer (conjSubgroup g A : Set G))) :=
        { elem := hBel
          ti := hBti
          conj := ⟨g⁻¹, hAconj⟩
          hL := rfl
          hLb := rfl
          hM := rfl
          ne_bot := fun hbot => hx1 (by
            have hxL : x ∈ conjSubgroup g A ⊓ normalizer (A : Set G) :=
              Subgroup.mem_inf.mpr ⟨hxg, hxN⟩
            rw [hbot, Subgroup.mem_bot] at hxL
            exact hxL)
          ne := fun heq => hBN fun y hy => by
            have hy' : y ∈ conjSubgroup g A ⊓ normalizer (A : Set G) := by
              rw [heq]
              exact hy
            exact (Subgroup.mem_inf.mp hy').2 }
      have S := hS0.symm
      have hxLb : x ∈ conjSubgroup g A ⊓ normalizer (A : Set G) :=
        Subgroup.mem_inf.mpr ⟨hxg, hxN⟩
      have hLx : ∀ c ∈ A, c ∈ A ⊓ normalizer (conjSubgroup g A : Set G) ↔ c * x = x * c := by
        intro c hc
        constructor
        · intro hcL
          exact S.comm_L_Lb hcL hxLb
        · intro hcx
          exact S.mem_L_of_commute hc hxg hx1 hcx
      have hA0L : Section3.A0 A Abar ≤ A ⊓ normalizer (conjSubgroup g A : Set G) := by
        by_contra hnot
        obtain ⟨c, hcA0, hcL⟩ := SetLike.not_le_iff_exists.mp hnot
        have hstar : ∀ a' ∈ A, a' ∉ A ⊓ normalizer (conjSubgroup g A : Set G) →
            a' ∈ Section3.A0 A Abar := by
          intro a' ha' ha'L
          obtain ⟨g', hg', hc'⟩ := S.tim77_2_4_five hCen hU (hS.L_le hcA0) hcL ha' ha'L
          rw [← hc']
          exact hA0norm g' (Subgroup.mem_inf.mp hg').2 c hcA0
        obtain ⟨u, huA, huL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
        obtain ⟨v, hvA, hvA0⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hS.L_le hA0ne)
        have huA0 : u ∈ Section3.A0 A Abar := hstar u huA huL
        have hvL : v ∈ A ⊓ normalizer (conjSubgroup g A : Set G) := by
          by_contra hvL
          exact hvA0 (hstar v hvA hvL)
        by_cases huvL : u * v ∈ A ⊓ normalizer (conjSubgroup g A : Set G)
        · apply huL
          have e : u = u * v * v⁻¹ := by group
          rw [e]
          exact Subgroup.mul_mem _ huvL (Subgroup.inv_mem _ hvL)
        · have huv : u * v ∈ Section3.A0 A Abar :=
            hstar (u * v) (Subgroup.mul_mem _ huA hvA) huvL
          apply hvA0
          have e : v = u⁻¹ * (u * v) := by group
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ huA0) huv
      have hLA0 : A ⊓ normalizer (conjSubgroup g A : Set G) ≤ Section3.A0 A Abar := by
        by_contra hnot
        obtain ⟨l, hlL, hlA0⟩ := SetLike.not_le_iff_exists.mp hnot
        have hprod := Subgroup.relIndex_mul_relIndex _ _ _ hA0L S.L_le
        rw [hidx] at hprod
        have hp1 : (Section3.A0 A Abar).relIndex
            (A ⊓ normalizer (conjSubgroup g A : Set G)) ≠ 1 := by
          rw [Ne, Subgroup.relIndex_eq_one]
          exact fun hle => hlA0 (hle hlL)
        have hq1 : (A ⊓ normalizer (conjSubgroup g A : Set G)).relIndex A ≠ 1 := by
          rw [Ne, Subgroup.relIndex_eq_one]
          exact fun hle => S.ne (le_antisymm S.L_le hle)
        have key : ∀ p q : ℕ, p * q = 2 → p ≠ 1 → q ≠ 1 → False := by
          intro p q hpq hp hq'
          have hp0 : p ≠ 0 := by
            rintro rfl
            simp at hpq
          have hq0 : q ≠ 0 := by
            rintro rfl
            simp at hpq
          have h22 : 2 * 2 ≤ p * q := Nat.mul_le_mul (by omega) (by omega)
          rw [hpq] at h22
          norm_num at h22
        exact key _ _ hprod hp1 hq1
      have hA0eqL : Section3.A0 A Abar = A ⊓ normalizer (conjSubgroup g A : Set G) :=
        le_antisymm hA0L hLA0
      rw [hA0eqL]
      ext c
      constructor
      · intro hc
        have hcA : c ∈ A := (Subgroup.mem_inf.mp hc).1
        refine Subgroup.mem_inf.mpr ⟨hcA, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        rw [Set.mem_singleton_iff.mp hd]
        exact ((hLx c hcA).mp hc).symm
      · intro hc
        have hcA : c ∈ A := (Subgroup.mem_inf.mp hc).1
        have hcx : c * x = x * c := by
          have hc' := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 x
            (Set.mem_singleton x)
          exact hc'.symm
        exact (hLx c hcA).mpr hcx
  exact ⟨hTIA0, hconj2, hA0norm, hconj4⟩

end CFSG.RankThree.GF2n.Tim77
