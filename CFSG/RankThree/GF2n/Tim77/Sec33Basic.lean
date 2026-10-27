module

public import CFSG.RankThree.GF2n.Tim77.Sec32d
public import CFSG.RankThree.GF2n.Tim77.Sec34
public import CFSG.RankThree.GF2n.Tim77.Sec3Conj
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import CFSG.RankThree.GF2n.Tim77.Sec32a
public import CFSG.RankThree.GF2n.Tim77.Sec41

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

theorem sec33_A0_le_N {A Abar : Subgroup G} {s : G} :
    Section3.A0 A Abar ≤ Section3.N A Abar s := by
  unfold Section3.N
  exact le_sup_left.trans le_sup_left

theorem sec33_Abar0_le_N {A Abar : Subgroup G} {s : G} :
    Section3.Abar0 A Abar ≤ Section3.N A Abar s := by
  unfold Section3.N
  exact le_sup_right.trans le_sup_left

theorem sec33_conj_Abar0_le_N {A Abar : Subgroup G} {s : G} :
    conjSubgroup s (Section3.Abar0 A Abar) ≤ Section3.N A Abar s := by
  unfold Section3.N
  exact le_sup_right

theorem sec33_sq_Abar0 [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) {x : G}
    (hx : x ∈ Section3.Abar0 A Abar) : x * x = 1 :=
  h.setup.sq_Ab (h.setup.Lb_le hx)

theorem sec33_sq_mem_N [Finite G] {A Abar S₀ B : Subgroup G} {s : G} (h : Sec3Ctx A Abar S₀ B)
    (hs : Section3.IsSChoice A Abar S₀ B s) : s * s ∈ Section3.N A Abar s := by
  obtain ⟨b, hb, hb1, hcase⟩ := hs
  have hbb : b * b = 1 := by
    obtain ⟨g, hg⟩ := h.nota.conj
    rw [← sq]
    exact (isElemAbelian_conj h.hyp.elemAbelian g).2 b (hg ▸ hb)
  rcases hcase with ⟨_, hsb⟩ | ⟨_, x, hx, hx1, hsx, hsS, hsC, hne, hcomm, hord⟩
  · subst hsb
    rw [hbb]
    exact Subgroup.one_mem _
  · have hxx : x * x = 1 := sec33_sq_Abar0 h hx
    have hs4 : s ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one s
    have hsq : (s * s) * (s * s) = 1 := by
      calc (s * s) * (s * s) = s ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := hs4
    rcases sec34_closure_pair hxx hbb hsx with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hxs : x * s * x = s⁻¹ := by
        rw [hi, sec34_conj_zpow hxx hbb i, zpow_neg]
      have key : s * s = x * (s * x * s⁻¹) := by
        calc s * s = (s * s)⁻¹ := (inv_eq_of_mul_eq_one_right hsq).symm
          _ = s⁻¹ * s⁻¹ := by group
          _ = (x * s * x) * s⁻¹ := by rw [hxs]
          _ = x * (s * x * s⁻¹) := by group
      rw [key]
      refine Subgroup.mul_mem _ (sec33_Abar0_le_N hx) (sec33_conj_Abar0_le_N ?_)
      exact (mem_conjSubgroup_conj_t77 s x _).2 hx
    · exfalso
      have hs' : s = (x * b) ^ i * x := by
        rw [← hi, mul_assoc, hxx, mul_one]
      have h1 : s * s = 1 := by
        rw [hs']
        calc (x * b) ^ i * x * ((x * b) ^ i * x)
            = (x * b) ^ i * (x * (x * b) ^ i * x) := by group
          _ = (x * b) ^ i * (x * b) ^ (-i) := by rw [sec34_conj_zpow hxx hbb i]
          _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero]
      have h2 : s ^ 2 = 1 := by rw [sq]; exact h1
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hord] at h3
      norm_num at h3


theorem sec33_conj_comm {a s y : G} (h : s * a = a * s) :
    a * (s * y * s⁻¹) * a⁻¹ = s * (a * y * a⁻¹) * s⁻¹ := by
  have h1 : a * s = s * a := h.symm
  have h2 : s⁻¹ * a⁻¹ = a⁻¹ * s⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, h1]
  calc a * (s * y * s⁻¹) * a⁻¹ = (a * s) * y * (s⁻¹ * a⁻¹) := by group
    _ = (s * a) * y * (a⁻¹ * s⁻¹) := by rw [h1, h2]
    _ = s * (a * y * a⁻¹) * s⁻¹ := by group

theorem sec33_conj_mem_N [Finite G] {A Abar S₀ B : Subgroup G} {s : G} (h : Sec3Ctx A Abar S₀ B)
    (hs : Section3.IsSChoice A Abar S₀ B s) :
    ∀ n ∈ Section3.N A Abar s, s * n * s⁻¹ ∈ Section3.N A Abar s := by
  have hsA : ∀ a ∈ A, s * a = a * s := (sec32a_s_facts h hs).2
  obtain ⟨hNY, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  have hNc : ∀ x ∈ Section3.N A Abar s, ∀ w ∈ Section3.N A Abar s, x * w = w * x :=
    fun x hx w hw => congrArg Subtype.val (hNab.1.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩)
  have hsq := sec33_sq_mem_N h hs
  have hle : Section3.N A Abar s ≤
      (Section3.N A Abar s).comap (MulAut.conj s).toMonoidHom := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      show s * x * s⁻¹ ∈ Section3.N A Abar s
      rw [sec32a_conj_eq_of_comm (hsA x (h.setup.L_le hx))]
      exact sec33_A0_le_N hx
    · intro x hx
      exact sec33_conj_Abar0_le_N ((mem_conjSubgroup_conj_t77 s x _).2 hx)
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := (mem_conjSubgroup_exists_t77 s _ x).1 hx
      have hcm := hNc (s * s) hsq y (sec33_Abar0_le_N hy)
      have e : s * (s * y * s⁻¹) * s⁻¹ = y := by
        calc s * (s * y * s⁻¹) * s⁻¹ = (s * s) * y * (s * s)⁻¹ := by group
          _ = (y * (s * s)) * (s * s)⁻¹ := by rw [hcm]
          _ = y := by group
      show s * (s * y * s⁻¹) * s⁻¹ ∈ Section3.N A Abar s
      rw [e]
      exact sec33_Abar0_le_N hy
  intro n hn
  exact hle hn

theorem sec33_fixed_comm [Finite G] {A Abar S₀ B : Subgroup G} {s : G}
    (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    (hne : conjSubgroup s Abar ≠ Abar) {z : G} (hz : z ∈ Section3.N A Abar s)
    (hsz : s * z * s⁻¹ = z) {a : G} (ha : a ∈ A) : a * z = z * a := by
  have hsA : ∀ a ∈ A, s * a = a * s := (sec32a_s_facts h hs).2
  obtain ⟨hNY, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  have hNc : ∀ x ∈ Section3.N A Abar s, ∀ w ∈ Section3.N A Abar s, x * w = w * x :=
    fun x hx w hw => congrArg Subtype.val (hNab.1.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩)
  have hsq : s * s ∈ Section3.N A Abar s := sec33_sq_mem_N h hs
  have hcomm1 : ∀ m ∈ Section3.A0 A Abar ⊔ Section3.Abar0 A Abar,
      ∀ w ∈ conjSubgroup s (Section3.Abar0 A Abar), m * w = w * m := fun m hm w hw =>
    hNc m (sup_le sec33_A0_le_N sec33_Abar0_le_N hm) w (sec33_conj_Abar0_le_N hw)
  have hz' : z ∈ (Section3.A0 A Abar ⊔ Section3.Abar0 A Abar) ⊔
      conjSubgroup s (Section3.Abar0 A Abar) := hz
  obtain ⟨m, hm, w, hw, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm1 hz'
  obtain ⟨a₀, ha₀, y, hy, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun l hl y hy => h.setup.comm_L_Lb hl hy) hm
  obtain ⟨y', hy', rfl⟩ : ∃ y' ∈ Section3.Abar0 A Abar, w = s * y' * s⁻¹ :=
    ⟨s⁻¹ * w * s, mem_conjSubgroup.mp hw, by group⟩
  have hyN : y ∈ Section3.N A Abar s := sec33_Abar0_le_N hy
  have hy'N : y' ∈ Section3.N A Abar s := sec33_Abar0_le_N hy'
  have hPN : s * y * s⁻¹ ∈ Section3.N A Abar s := sec33_conj_Abar0_le_N
    ((mem_conjSubgroup_conj_t77 s y _).2 hy)
  have hQN : s * y' * s⁻¹ ∈ Section3.N A Abar s := sec33_conj_Abar0_le_N
    ((mem_conjSubgroup_conj_t77 s y' _).2 hy')
  have ha₀A : a₀ ∈ A := h.setup.L_le ha₀
  have hQQ : s * (s * y' * s⁻¹) * s⁻¹ = y' := by
    have hcm := hNc (s * s) hsq y' hy'N
    calc s * (s * y' * s⁻¹) * s⁻¹ = (s * s) * y' * (s * s)⁻¹ := by group
      _ = (y' * (s * s)) * (s * s)⁻¹ := by rw [hcm]
      _ = y' := by group
  have hlhs : s * (a₀ * y * (s * y' * s⁻¹)) * s⁻¹ = a₀ * (s * y * s⁻¹) * y' := by
    calc s * (a₀ * y * (s * y' * s⁻¹)) * s⁻¹
        = (s * a₀ * s⁻¹) * (s * y * s⁻¹) * (s * (s * y' * s⁻¹) * s⁻¹) := by group
      _ = a₀ * (s * y * s⁻¹) * y' := by rw [sec32a_conj_eq_of_comm (hsA a₀ ha₀A), hQQ]
  have hfix : a₀ * (s * y * s⁻¹) * y' = a₀ * y * (s * y' * s⁻¹) := by
    rw [← hlhs]
    exact hsz
  have hfix' : (s * y * s⁻¹) * y' = y * (s * y' * s⁻¹) := by
    have h1 : a₀ * ((s * y * s⁻¹) * y') = a₀ * (y * (s * y' * s⁻¹)) := by
      simpa only [mul_assoc] using hfix
    exact mul_left_cancel h1
  have hu : s * (y * y'⁻¹) * s⁻¹ = y * y'⁻¹ := by
    have hP : s * y * s⁻¹ = (y * (s * y' * s⁻¹)) * y'⁻¹ := eq_mul_inv_of_mul_eq hfix'
    have hcQ : (s * y' * s⁻¹) * y'⁻¹ = y'⁻¹ * (s * y' * s⁻¹) :=
      hNc _ hQN _ (Subgroup.inv_mem _ hy'N)
    calc s * (y * y'⁻¹) * s⁻¹ = (s * y * s⁻¹) * (s * y' * s⁻¹)⁻¹ := by group
      _ = ((y * (s * y' * s⁻¹)) * y'⁻¹) * (s * y' * s⁻¹)⁻¹ := by rw [hP]
      _ = y * ((s * y' * s⁻¹) * y'⁻¹) * (s * y' * s⁻¹)⁻¹ := by group
      _ = y * (y'⁻¹ * (s * y' * s⁻¹)) * (s * y' * s⁻¹)⁻¹ := by rw [hcQ]
      _ = y * y'⁻¹ := by group
  have hu0 : y * y'⁻¹ ∈ Section3.Abar0 A Abar :=
    Subgroup.mul_mem _ hy (Subgroup.inv_mem _ hy')
  have hu1 : y * y'⁻¹ ∈ Abar ⊓ conjSubgroup s Abar := by
    refine Subgroup.mem_inf.mpr ⟨h.setup.Lb_le hu0, ?_⟩
    have := (mem_conjSubgroup_conj_t77 s (y * y'⁻¹) Abar).2 (h.setup.Lb_le hu0)
    rwa [hu] at this
  rw [inf_conjSubgroup_eq_bot_of_isTI h.setup.ti_Ab hne, Subgroup.mem_bot] at hu1
  have hyy : y = y' := mul_inv_eq_one.mp hu1
  subst hyy
  have hc : a * y * a⁻¹ * y⁻¹ ∈ Section3.A0 A Abar := h.setup.commutator_mem_L ha hy
  set c := a * y * a⁻¹ * y⁻¹ with hcdef
  have hcA : c ∈ A := h.setup.L_le hc
  have hcy : c * y = y * c := h.setup.comm_L_Lb hc hy
  have hcc : c * c = 1 := h.setup.sq_A hcA
  have hay : a * y * a⁻¹ = c * y := by rw [hcdef]; group
  have haa₀ : a * a₀ * a⁻¹ = a₀ := by rw [h.setup.comm_A ha ha₀A]; group
  have hconj : a * (a₀ * y * (s * y * s⁻¹)) * a⁻¹ = a₀ * y * (s * y * s⁻¹) := by
    calc a * (a₀ * y * (s * y * s⁻¹)) * a⁻¹
        = (a * a₀ * a⁻¹) * (a * y * a⁻¹) * (a * (s * y * s⁻¹) * a⁻¹) := by group
      _ = a₀ * (c * y) * (s * (c * y) * s⁻¹) := by
          rw [haa₀, sec33_conj_comm (hsA a ha), hay]
      _ = a₀ * (c * y) * (c * (s * y * s⁻¹)) := by
          rw [show s * (c * y) * s⁻¹ = (s * c * s⁻¹) * (s * y * s⁻¹) by group,
            sec32a_conj_eq_of_comm (hsA c hcA)]
      _ = a₀ * (c * (y * c)) * (s * y * s⁻¹) := by group
      _ = a₀ * (c * (c * y)) * (s * y * s⁻¹) := by rw [← hcy]
      _ = a₀ * ((c * c) * y) * (s * y * s⁻¹) := by group
      _ = a₀ * y * (s * y * s⁻¹) := by rw [hcc, one_mul]
  have := hconj
  rwa [mul_inv_eq_iff_eq_mul] at this


theorem sec33_N_le_normalizer_conj [Finite G] {A Abar S₀ B : Subgroup G} {s : G}
    (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s) {y : G}
    (hy : y ∈ Section3.Y A Abar s) :
    ∀ n ∈ Section3.N A Abar s, n ∈ normalizer (conjSubgroup y A : Set G) := by
  intro n hn
  obtain ⟨hNY, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  have hn' : y⁻¹ * n * y ∈ Section3.N A Abar s := by
    have := (Subgroup.mem_normalizer_iff.mp (hYN y⁻¹ (inv_mem hy)) n).mp hn
    simpa using this
  have hA := sec32d_N_le_normalizer h (sec32d_mem_centralizer h hs) hn'
  rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_conjSubgroup,
    show n * y = y * (y⁻¹ * n * y) by group, ← conjSubgroup_conjSubgroup,
    mem_normalizer_iff_conjSubgroup_eq.mp hA]

theorem sec33_comm_of_fixed [Finite G] {A Abar S₀ B : Subgroup G} {s : G}
    (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    (hne : conjSubgroup s Abar ≠ Abar) {k : G} (hk : k ∈ Section3.Y A Abar s) {n : G}
    (hn : n ∈ Section3.N A Abar s) (hkn : s * k * s⁻¹ = k * n) :
    ∀ x ∈ A, ∀ w ∈ conjSubgroup k A, x * w = w * x := by
  by_contra hnc
  obtain ⟨hNY, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  have hNc : ∀ x ∈ Section3.N A Abar s, ∀ w ∈ Section3.N A Abar s, x * w = w * x :=
    fun x hx w hw => congrArg Subtype.val (hNab.1.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩)
  have hsA : ∀ a ∈ A, s * a = a * s := (sec32a_s_facts h hs).2
  obtain ⟨a₀, ha₀, ha₀1⟩ := sec32a_exists_mem_ne_one h.a0_ne_bot
  have ha₀N : a₀ ∈ Section3.N A Abar s := sec33_A0_le_N ha₀
  have hzN : k * a₀ * k⁻¹ ∈ Section3.N A Abar s :=
    (Subgroup.mem_normalizer_iff.mp (hYN k hk) a₀).mp ha₀N
  have hsa₀ : s * a₀ * s⁻¹ = a₀ := sec32a_conj_eq_of_comm (hsA a₀ (h.setup.L_le ha₀))
  have hna : n * a₀ * n⁻¹ = a₀ := by
    rw [hNc n hn a₀ ha₀N]
    group
  have hsz : s * (k * a₀ * k⁻¹) * s⁻¹ = k * a₀ * k⁻¹ := by
    calc s * (k * a₀ * k⁻¹) * s⁻¹
        = (s * k * s⁻¹) * (s * a₀ * s⁻¹) * (s * k * s⁻¹)⁻¹ := by group
      _ = (k * n) * a₀ * (k * n)⁻¹ := by rw [hkn, hsa₀]
      _ = k * (n * a₀ * n⁻¹) * k⁻¹ := by group
      _ = k * a₀ * k⁻¹ := by rw [hna]
  have hnc' : ¬ ∀ x ∈ conjSubgroup 1 A, ∀ w ∈ conjSubgroup k A, x * w = w * x :=
    fun hall => hnc fun x hx w hw => hall x (by rwa [conjSubgroup_one]) w hw
  have S := sec41_prop24 h hYN hNc (one_mem _) hk hnc'
  rw [conjSubgroup_one, conjSubgroup_one] at S
  have hzLb : k * a₀ * k⁻¹ ∈ conjSubgroup k (Section3.A0 A Abar) :=
    (mem_conjSubgroup_conj_t77 k a₀ _).2 ha₀
  have hzM : k * a₀ * k⁻¹ ∈ Section3.A0 A Abar ⊔ conjSubgroup k (Section3.A0 A Abar) :=
    S.Lb_le_M hzLb
  obtain ⟨t, htA, htL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h.setup.L_le h.a0_ne)
  have hcomm : t * (k * a₀ * k⁻¹) = (k * a₀ * k⁻¹) * t :=
    sec33_fixed_comm h hs hne hzN hsz htA
  have hzL : k * a₀ * k⁻¹ ∈ Section3.A0 A Abar := S.mem_L_of_commute_M htA htL hzM hcomm
  have hz1 : k * a₀ * k⁻¹ ∈ A ⊓ conjSubgroup k A :=
    Subgroup.mem_inf.mpr ⟨h.setup.L_le hzL, S.Lb_le hzLb⟩
  rw [S.inf_eq_bot, Subgroup.mem_bot] at hz1
  exact ha₀1 ((conj_eq_one_iff_t77 k a₀).1 hz1)

end CFSG.RankThree.GF2n.Tim77
