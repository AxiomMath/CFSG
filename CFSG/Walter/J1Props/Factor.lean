module

public import CFSG.Walter.J1Props.Orbit
public import CFSG.Walter.J1Props.Transfer
public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Walter.J1Props

open CFSG.Walter.J1Recog CFSG.Open Word

theorem eq_self_of_pow_odd {Q : Type*} [Group Q] {a : Q} (ha : a * a = 1) (k : ℕ) :
    a ^ (2 * k + 1) = a := by
  rw [pow_succ, pow_mul, pow_two, ha, one_pow, one_mul]

theorem eq_one_of_rels {Q : Type*} [Group Q] {a b c : Q} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hab : a * b = b * a) (h5 : (c * a) ^ 5 = 1) (h3 : (c * b) ^ 3 = 1)
    (h5' : (c * a * b) ^ 5 = 1) (h : a = 1 ∨ b = 1 ∨ a * b = 1 ∨ c * b = 1 ∨ c * a = 1) :
    a = 1 ∧ b = 1 ∧ c = 1 := by
  have p5 : ∀ x : Q, x * x = 1 → x ^ 5 = x := fun x hx => eq_self_of_pow_odd hx 2
  have p3 : ∀ x : Q, x * x = 1 → x ^ 3 = x := fun x hx => eq_self_of_pow_odd hx 1
  rcases h with h | h | h | h | h
  · subst h
    rw [mul_one, p5 c hc] at h5
    subst h5
    rw [one_mul, p3 b hb] at h3
    exact ⟨rfl, h3, rfl⟩
  · subst h
    rw [mul_one, p3 c hc] at h3
    subst h3
    rw [one_mul, p5 a ha] at h5
    exact ⟨h5, rfl, rfl⟩
  · have hb' : b = a := by
      calc b = (a * a) * b := by rw [ha, one_mul]
        _ = a * (a * b) := by rw [mul_assoc]
        _ = a := by rw [h, mul_one]
    rw [mul_assoc, h, mul_one, p5 c hc] at h5'
    subst h5'
    rw [one_mul, p5 a ha] at h5
    exact ⟨h5, hb'.trans h5, rfl⟩
  · have hc' : c = b := by
      calc c = c * (b * b) := by rw [hb, mul_one]
        _ = (c * b) * b := by rw [mul_assoc]
        _ = b := by rw [h, one_mul]
    subst hc'
    have hinv : (c * a * c) * (c * a * c) = 1 := by
      calc (c * a * c) * (c * a * c) = c * a * (c * c) * a * c := by group
        _ = 1 := by rw [hc, mul_one, mul_assoc c a a, ha, mul_one, hc]
    rw [p5 _ hinv] at h5'
    have ha1 : a = 1 := by
      calc a = c * (c * a * c) * c := by
            rw [← mul_assoc, ← mul_assoc, hc, one_mul, mul_assoc, hc, mul_one]
        _ = 1 := by rw [h5', mul_one, hc]
    subst ha1
    rw [mul_one, p5 c hc] at h5
    exact ⟨rfl, h5, h5⟩
  · have hc' : c = a := by
      calc c = c * (a * a) := by rw [ha, mul_one]
        _ = (c * a) * a := by rw [mul_assoc]
        _ = a := by rw [h, one_mul]
    subst hc'
    have hab2 : (c * b) * (c * b) = 1 := by
      calc (c * b) * (c * b) = c * (b * c) * b := by group
        _ = c * (c * b) * b := by rw [← hab]
        _ = 1 := by rw [← mul_assoc, hc, one_mul, hb]
    rw [p3 _ hab2] at h3
    have hb' : b = c := by
      calc b = (c * c) * b := by rw [hc, one_mul]
        _ = c * (c * b) := by rw [mul_assoc]
        _ = c := by rw [h3, mul_one]
    subst hb'
    have h15 : (b * b * b) ^ 5 = b := by
      rw [hb, one_mul, p5 b hb]
    rw [h15] at h5'
    exact ⟨h5', h5', h5'⟩

theorem isMulCommutative_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (hS : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a * b = b * a)
    (P : Sylow p G) : IsMulCommutative (P : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have ha : (a : G) ∈ ((g • S : Sylow p G) : Subgroup G) := hg ▸ a.2
  have hb : (b : G) ∈ ((g • S : Sylow p G) : Subgroup G) := hg ▸ b.2
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply] at ha hb
  have h := hS _ ha _ hb
  change (a : G) * b = b * a
  calc (a : G) * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
    _ = b * a := by group

theorem le_of_isPGroup_of_normal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {N H K : Subgroup G} [hN : N.Normal] (hH : IsPGroup p H) (hHi : ¬ p ∣ H.index)
    (hK : IsPGroup p K) (hKi : ¬ p ∣ K.index) (hHN : H ≤ N) : K ≤ N := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hH.toSylow hHi) (hK.toSylow hKi)
  intro x hx
  have hx' : x ∈ ((g • hH.toSylow hHi : Sylow p G) : Subgroup G) := by
    rw [hg]
    exact hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply] at hx'
  have hx'' : g⁻¹ * x * g ∈ H := hx'
  have := hN.conj_mem _ (hHN hx'') g
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this

open CFSG.Sporadic.Bridge.J1 in
theorem hasAbelianSylowTwo : HasAbelianSylowTwo walterJ1 := by
  have hle : elemAbelian ≤ walterJ1 := walterJ1_eq ▸ elemAbelian_le
  set E := elemAbelian.subgroupOf walterJ1 with hEdef
  have hE : Nat.card E = 8 := by
    rw [hEdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_elemAbelian]
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hE]; norm_num)
  have hidx : E.index = 21945 := by
    have := E.card_mul_index
    rw [hE, card_walterJ1] at this
    omega
  have hxor : ∀ i j : Fin 8, vXor i j = vXor j i := by decide
  intro P
  refine isMulCommutative_sylow (hE2.toSylow (by rw [hidx]; norm_num)) ?_ P
  intro a ha b hb
  change a ∈ E at ha
  change b ∈ E at hb
  rw [hEdef, Subgroup.mem_subgroupOf] at ha hb
  obtain ⟨i, hi⟩ := mem_elemAbelian.mp ha
  obtain ⟨j, hj⟩ := mem_elemAbelian.mp hb
  have hi' : mat a = vMat i := hi
  have hj' : mat b = vMat j := hj
  apply mat_injective
  rw [mat_mul, mat_mul, hi', hj', vMat_mul, vMat_mul, hxor]

@[expose] def wx : Word 5 := wt ++ Word.conj wt wn

@[expose] def wx' : Word 5 := wt ++ Word.conj wt (Word.pow wn 2)

noncomputable abbrev xJ : walterJ1 := elt wx

noncomputable abbrev x'J : walterJ1 := elt wx'

noncomputable abbrev FJ : Subgroup walterJ1 := Subgroup.closure {xJ, x'J, uJ}

theorem rels_F : xJ * xJ = 1 ∧ x'J * x'J = 1 ∧ uJ * uJ = 1 ∧ xJ * x'J = x'J * xJ ∧
    (uJ * xJ) ^ 5 = 1 ∧ (uJ * x'J) ^ 3 = 1 ∧ (uJ * xJ * x'J) ^ 5 = 1 := by
  simp only [← elt_append, ← elt_pow, elt_eq_one_iff, elt_eq_elt_iff]
  decide +kernel

theorem ne_one_F : xJ ≠ 1 ∧ x'J ≠ 1 ∧ xJ ≠ x'J ∧ uJ * xJ ≠ 1 ∧ uJ * x'J ≠ 1 ∧ tJ ≠ 1 := by
  simp only [ne_eq, ← elt_append, elt_eq_one_iff, elt_eq_elt_iff]
  decide +kernel

theorem commute_tJ : xJ * tJ = tJ * xJ ∧ x'J * tJ = tJ * x'J ∧ uJ * tJ = tJ * uJ := by
  simp only [← elt_append, elt_eq_elt_iff]
  decide +kernel

theorem tJ_mul_self : tJ * tJ = 1 := by
  simp only [← elt_append, elt_eq_one_iff]
  decide +kernel

theorem orderOf_tJ : orderOf tJ = 2 := J1.orderOf_eq_two_iff.mpr ⟨tJ_mul_self, ne_one_F.2.2.2.2.2⟩

theorem mem_F : xJ ∈ FJ ∧ x'J ∈ FJ ∧ uJ ∈ FJ :=
  ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
    Subgroup.subset_closure (by simp)⟩

theorem F_le_centralizer : FJ ≤ Subgroup.centralizer ({tJ} : Set walterJ1) := by
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exacts [commute_tJ.1, commute_tJ.2.1, commute_tJ.2.2]

theorem F_eq_top_of {N : Subgroup FJ} (ha : (⟨xJ, mem_F.1⟩ : FJ) ∈ N)
    (hb : (⟨x'J, mem_F.2.1⟩ : FJ) ∈ N) (hc : (⟨uJ, mem_F.2.2⟩ : FJ) ∈ N) : N = ⊤ := by
  rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := {xJ, x'J, uJ}),
    Subgroup.closure_le]
  rintro ⟨g, hg⟩ (h | h | h)
  · exact (Subtype.ext h : (⟨g, hg⟩ : FJ) = ⟨xJ, mem_F.1⟩) ▸ ha
  · exact (Subtype.ext h : (⟨g, hg⟩ : FJ) = ⟨x'J, mem_F.2.1⟩) ▸ hb
  · exact (Subtype.ext h : (⟨g, hg⟩ : FJ) = ⟨uJ, mem_F.2.2⟩) ▸ hc

theorem F_eq_top_of_mem {N : Subgroup FJ} [hN : N.Normal]
    (h : (⟨xJ, mem_F.1⟩ : FJ) ∈ N ∨ (⟨x'J, mem_F.2.1⟩ : FJ) ∈ N ∨
      (⟨xJ, mem_F.1⟩ * ⟨x'J, mem_F.2.1⟩ : FJ) ∈ N ∨
      (⟨uJ, mem_F.2.2⟩ * ⟨x'J, mem_F.2.1⟩ : FJ) ∈ N ∨
      (⟨uJ, mem_F.2.2⟩ * ⟨xJ, mem_F.1⟩ : FJ) ∈ N) : N = ⊤ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := rels_F
  set a : FJ := ⟨xJ, mem_F.1⟩
  set b : FJ := ⟨x'J, mem_F.2.1⟩
  set c : FJ := ⟨uJ, mem_F.2.2⟩
  let π := QuotientGroup.mk' N
  have e : ∀ {y z : FJ}, (y : walterJ1) = z → π y = π z := fun hyz => by rw [Subtype.ext hyz]
  have k1 : π a * π a = 1 := by rw [← map_mul, ← map_one π]; exact e h1
  have k2 : π b * π b = 1 := by rw [← map_mul, ← map_one π]; exact e h2
  have k3 : π c * π c = 1 := by rw [← map_mul, ← map_one π]; exact e h3
  have k4 : π a * π b = π b * π a := by rw [← map_mul, ← map_mul]; exact e h4
  have k5 : (π c * π a) ^ 5 = 1 := by rw [← map_mul, ← map_pow, ← map_one π]; exact e h5
  have k6 : (π c * π b) ^ 3 = 1 := by rw [← map_mul, ← map_pow, ← map_one π]; exact e h6
  have k7 : (π c * π a * π b) ^ 5 = 1 := by
    rw [← map_mul, ← map_mul, ← map_pow, ← map_one π]; exact e h7
  have hmem : ∀ y : FJ, y ∈ N ↔ π y = 1 := fun y => (QuotientGroup.eq_one_iff y).symm
  have hk : π a = 1 ∨ π b = 1 ∨ π a * π b = 1 ∨ π c * π b = 1 ∨ π c * π a = 1 := by
    simp only [← map_mul, ← hmem]
    exact h
  obtain ⟨ha, hb, hc⟩ := eq_one_of_rels k1 k2 k3 k4 k5 k6 k7 hk
  exact F_eq_top_of ((hmem a).mpr ha) ((hmem b).mpr hb) ((hmem c).mpr hc)

theorem F_perfect : commutator FJ = ⊤ := by
  rw [← Abelianization.ker_of]
  have hcomm : ∀ y z : Abelianization FJ, y * z = z * y := fun y z => mul_comm y z
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := rels_F
  set c : FJ := ⟨uJ, mem_F.2.2⟩
  set b : FJ := ⟨x'J, mem_F.2.1⟩
  have hb : b * b = 1 := Subtype.ext h2
  have hc : c * c = 1 := Subtype.ext h3
  have hcb : (c * b) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h6)
  apply F_eq_top_of_mem
  right; right; right; left
  rw [MonoidHom.mem_ker, map_mul]
  have kb : Abelianization.of b * Abelianization.of b = 1 := by rw [← map_mul, hb, map_one]
  have kc : Abelianization.of c * Abelianization.of c = 1 := by rw [← map_mul, hc, map_one]
  have k3 : (Abelianization.of c * Abelianization.of b) ^ 3 = 1 := by
    rw [← map_mul, ← map_pow, hcb, map_one]
  rwa [mul_pow, eq_self_of_pow_odd kc 1, eq_self_of_pow_odd kb 1] at k3

theorem F_index_ne_two (H : Subgroup FJ) (_ : H.Normal) : H.index ≠ 2 :=
  index_ne_of_perfect F_perfect H Nat.prime_two

theorem tJ_not_mem_F : tJ ∉ FJ := by
  intro htF
  set z : FJ := ⟨tJ, htF⟩
  have hz2 : orderOf z = 2 := by rw [← Subgroup.orderOf_coe]; exact orderOf_tJ
  obtain ⟨P, hP⟩ := (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one]) :
    IsPGroup 2 (Subgroup.zpowers z)).exists_le_sylow
  have hPab : IsMulCommutative (P : Subgroup FJ) := by
    obtain ⟨S', hS'⟩ := (P.isPGroup'.map FJ.subtype).exists_le_sylow
    have hc := hasAbelianSylowTwo S'
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha : ((a : FJ) : walterJ1) ∈ (S' : Subgroup walterJ1) := hS' ⟨a, a.2, rfl⟩
    have hb : ((b : FJ) : walterJ1) ∈ (S' : Subgroup walterJ1) := hS' ⟨b, b.2, rfl⟩
    have hab := congrArg Subtype.val (hc.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    exact Subtype.ext (Subtype.ext hab)
  have h1 := eq_one_of_mem_sylow_of_commute_normalizer F_index_ne_two P
    (hP (Subgroup.mem_zpowers z)) (fun n _ =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (F_le_centralizer n.2)))
  exact ne_one_F.2.2.2.2.2 (congrArg Subtype.val h1)

theorem zpowers_tJ_le_normalizer :
    Subgroup.zpowers tJ ≤ Subgroup.normalizer (FJ : Set walterJ1) := by
  rw [Subgroup.zpowers_le]
  refine J1.mem_normalizer_of_conj_mem fun x hx => ?_
  rw [← Subgroup.mem_centralizer_singleton_iff.mp (F_le_centralizer hx), mul_inv_cancel_right]
  exact hx

theorem card_sup_F : Nat.card (Subgroup.zpowers tJ ⊔ FJ : Subgroup walterJ1) =
    Nat.card FJ * 2 := by
  rw [sup_comm, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    zpowers_tJ_le_normalizer, Nat.card_zpowers, orderOf_tJ]
  rw [Subgroup.disjoint_def]
  intro y hyF hy
  rcases (J1.mem_zpowers_of_orderOf_eq_two orderOf_tJ).mp hy with rfl | rfl
  · rfl
  · exact absurd hyF tJ_not_mem_F

theorem sixty_dvd_card_F : 60 ∣ Nat.card FJ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := rels_F
  obtain ⟨n1, n2, n3, n4, n5, -⟩ := ne_one_F
  let V := GorensteinWalter.kleinFourOfCommutingInvolutions xJ x'J h1 h2 h4
  have hV : Nat.card V = 4 :=
    (GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions xJ x'J h1 h2 n1 n2 n3
      h4).card_four
  have hVF : V ≤ FJ := by
    intro y hy
    change y ∈ ({xJ * x'J, xJ, x'J, 1} : Set walterJ1) at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact FJ.mul_mem mem_F.1 mem_F.2.1
    · exact mem_F.1
    · exact mem_F.2.1
    · exact FJ.one_mem
  have h4d : 4 ∣ Nat.card FJ := hV ▸ Subgroup.card_dvd_of_le hVF
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h3d : 3 ∣ Nat.card FJ := by
    have : orderOf (uJ * x'J) = 3 := orderOf_eq_prime h6 n5
    exact this ▸ Subgroup.orderOf_dvd_natCard FJ (FJ.mul_mem mem_F.2.2 mem_F.2.1)
  have h5d : 5 ∣ Nat.card FJ := by
    have : orderOf (uJ * xJ) = 5 := orderOf_eq_prime h5 n4
    exact this ▸ Subgroup.orderOf_dvd_natCard FJ (FJ.mul_mem mem_F.2.2 mem_F.1)
  have h12 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 3) h4d h3d
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 12 5) h12 h5d

theorem card_centralizer_tJ : Nat.card (Subgroup.centralizer ({tJ} : Set walterJ1)) = 120 := by
  set C := Subgroup.centralizer ({tJ} : Set walterJ1)
  have hle : Subgroup.zpowers tJ ⊔ FJ ≤ C :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
      F_le_centralizer
  have h120 : 120 ∣ Nat.card C := by
    have := Subgroup.card_dvd_of_le hle
    rw [card_sup_F] at this
    obtain ⟨k, hk⟩ := sixty_dvd_card_F
    rw [hk] at this
    exact (Dvd.intro_left _ (by ring) : 120 ∣ 60 * k * 2).trans this
  have hdvd : Nat.card C ∣ 175560 := card_walterJ1 ▸ Subgroup.card_subgroup_dvd_card C
  have hle836 := card_centralizer_tJ_le
  obtain ⟨k, hk⟩ := h120
  have hpos : 0 < Nat.card C := Nat.card_pos
  rw [hk] at hdvd hle836 hpos ⊢
  have hk6 : k ≤ 6 := by omega
  interval_cases k <;> omega

theorem card_F : Nat.card FJ = 60 := by
  have hle : Subgroup.zpowers tJ ⊔ FJ ≤ Subgroup.centralizer ({tJ} : Set walterJ1) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
      F_le_centralizer
  have h1 := Subgroup.card_le_of_le hle
  rw [card_sup_F, card_centralizer_tJ] at h1
  obtain ⟨k, hk⟩ := sixty_dvd_card_F
  have hpos : 0 < Nat.card FJ := Nat.card_pos
  omega

theorem centralizer_tJ_eq :
    Subgroup.centralizer ({tJ} : Set walterJ1) = Subgroup.zpowers tJ ⊔ FJ := by
  have hle : Subgroup.zpowers tJ ⊔ FJ ≤ Subgroup.centralizer ({tJ} : Set walterJ1) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
      F_le_centralizer
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_sup_F, card_centralizer_tJ, card_F]

end CFSG.Walter.J1Props
