module

public import CFSG.Walter.ReeOrder.JT.Section4E
public import CFSG.Walter.ReeOrder.JT.Cited
public import CFSG.Walter.ReeOrder.JT.PSL24

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups

section DirectProduct

variable {X : Type*} [Group X] {A B H : Subgroup X}

theorem IsInternalDirectProduct.exists_mul (hd : IsInternalDirectProduct A B H) {x : X}
    (hx : x ∈ H) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  obtain ⟨hsup, -, hAC⟩ := hd
  have hle : A ≤ Subgroup.normalizer (B : Set X) := hAC.trans (Subgroup.centralizer_le_normalizer _)
  rw [← hsup, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := hx
  exact ⟨a, ha, b, hb, hab⟩

theorem IsInternalDirectProduct.commute (hd : IsInternalDirectProduct A B H) {a b : X}
    (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a :=
  ((Subgroup.mem_centralizer_iff.mp (hd.2.2 ha)) b hb).symm

theorem IsInternalDirectProduct.left_le (hd : IsInternalDirectProduct A B H) : A ≤ H :=
  hd.1 ▸ le_sup_left

theorem IsInternalDirectProduct.right_le (hd : IsInternalDirectProduct A B H) : B ≤ H :=
  hd.1 ▸ le_sup_right

theorem IsInternalDirectProduct.conj_mem_left (hd : IsInternalDirectProduct A B H) {g : X}
    (hg : g ∈ H) {a : X} (ha : a ∈ A) : g * a * g⁻¹ ∈ A := by
  obtain ⟨a', ha', b', hb', rfl⟩ := hd.exists_mul hg
  rw [show a' * b' * a * (a' * b')⁻¹ = a' * (b' * a * b'⁻¹) * a'⁻¹ by group,
    ← hd.commute ha hb', mul_inv_cancel_right]
  exact A.mul_mem (A.mul_mem ha' ha) (A.inv_mem ha')

theorem IsInternalDirectProduct.conj_mem_right (hd : IsInternalDirectProduct A B H) {g : X}
    (hg : g ∈ H) {b : X} (hb : b ∈ B) (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    g * b * g⁻¹ ∈ B := by
  obtain ⟨a', ha', b', hb', rfl⟩ := hd.exists_mul hg
  rw [show a' * b' * b * (a' * b')⁻¹ = a' * (b' * b * b'⁻¹) * a'⁻¹ by group,
    hBab b' hb' b hb, mul_inv_cancel_right, hd.commute ha' hb, mul_inv_cancel_right]
  exact hb

theorem IsInternalDirectProduct.mem_right_of_centralizes (hd : IsInternalDirectProduct A B H)
    (hZ : ∀ z ∈ A, (∀ y ∈ A, z * y = y * z) → z = 1) {x : X} (hx : x ∈ H)
    (hxA : ∀ y ∈ A, x * y = y * x) : x ∈ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hd.exists_mul hx
  have : a = 1 := hZ a ha fun y hy => by
    have h1 := hxA y hy
    have h2 := hd.commute hy hb
    calc a * y = a * b * y * b⁻¹ := by
          rw [mul_assoc a b y, ← h2]; group
      _ = y * (a * b) * b⁻¹ := by rw [h1]
      _ = y * a := by group
  rw [this, one_mul]
  exact hb

end DirectProduct

theorem nonempty_sup_zpowers_mulEquiv_dihedralGroup {X : Type*} [Group X] [Finite X]
    (U : Subgroup X) (hU : IsCyclic U) (w : X) (hwU : w ∉ U) (hw : w * w = 1)
    (hinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹) :
    Nonempty (↥(U ⊔ Subgroup.zpowers w) ≃* DihedralGroup (Nat.card U)) := by
  obtain ⟨u, hu⟩ := hU.exists_generator
  set D := U ⊔ Subgroup.zpowers w with hD
  have hUD : U ≤ D := le_sup_left
  have hwD : w ∈ D := le_sup_right (a := U) (Subgroup.mem_zpowers w)
  let ρ : D := ⟨u, hUD u.2⟩
  let σ : D := ⟨w, hwD⟩
  have hUeq : U = Subgroup.zpowers (u : X) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := hu ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rintro ⟨k, rfl⟩
      exact U.zpow_mem u.2 k
  have hgen : (⊤ : Subgroup D) = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    change D = Subgroup.zpowers (u : X) ⊔ Subgroup.zpowers w
    rw [hD, ← hUeq]
  have hσ2 : σ ^ 2 = 1 := Subtype.ext (by simp [σ, pow_two, hw])
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (by simp [σ, ρ, hinv u u.2])
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    rintro ⟨k, hk⟩
    apply hwU
    have h := congrArg Subtype.val hk
    simp only [Subgroup.coe_zpow, ρ, σ] at h
    rw [← h]
    exact U.zpow_mem u.2 k
  obtain ⟨e⟩ := GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have hord : orderOf ρ = Nat.card U := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hu]
  rw [hord] at e
  exact ⟨e⟩

theorem eq_one_of_mem_center_of_isSimpleGroup {X : Type*} [Group X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) {z : X} (hz : ∀ y, z * y = y * z) : z = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
  · exact Subgroup.mem_bot.mp (h1 ▸ Subgroup.mem_center_iff.mpr fun y => (hz y).symm)
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top b) a)

namespace IndexTwo

variable {G : Type} [Group G] [Finite G] {h : JTHyp G} {c : Config h} {R : Subgroup G}
  (d : IndexTwo (Subgroup.normalizer (R : Set G)))

theorem isKleinFour_sylow
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) (P : Sylow 2 d.M) :
    IsKleinFour (P : Subgroup d.M) := by
  have hcard : Nat.card (P : Subgroup d.M) = 4 := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity (d.sylow hp hRQ),
      d.coe_sylow hp hRQ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
      d.card_S_inf hp hRQ]
  refine ⟨hcard, ?_⟩
  obtain ⟨S'', hS''⟩ := (P.isPGroup'.map d.M.subtype).exists_le_sylow
  have hE := ((lemma_2_1 h hp).2.1 S'').1
  have hpow : ∀ y : (P : Subgroup d.M), y ^ 2 = 1 := fun y => by
    have hy : ((y : d.M) : G) ∈ (S'' : Subgroup G) := hS'' ⟨y, y.2, rfl⟩
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := (S'' : Subgroup G)) _ hy
    exact Subtype.ext (Subtype.ext (by simpa using this))
  have hdvd : Monoid.exponent (P : Subgroup d.M) ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exfalso
    have : Subsingleton (P : Subgroup d.M) := Monoid.exp_eq_one_iff.mp h1
    have := Nat.card_unique (α := (P : Subgroup d.M))
    omega
  · exact h1

theorem isConj
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) (x y : d.M) (hx : orderOf x = 2)
    (hy : orderOf y = 2) : IsConj x y := by
  rw [← Subgroup.orderOf_coe] at hx hy
  obtain ⟨g, hgM, hg⟩ := d.exists_conj_of_orderOf_eq_two hp hRQ x.2 y.2 hx hy
  exact isConj_iff.mpr ⟨⟨g, hgM⟩, Subtype.ext hg⟩

theorem isMulCommutative_centralizer
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) (hR : R ≠ ⊥) (x : d.M)
    (hx : orderOf x = 2) : IsMulCommutative (Subgroup.centralizer ({x} : Set d.M)) := by
  have hTM : c.T ≤ d.M := by
    rw [← d.S_inf_eq_T hp hRQ hR]; exact inf_le_right
  rw [← Subgroup.orderOf_coe] at hx
  obtain ⟨g, hgM, hg⟩ := d.exists_conj_of_orderOf_eq_two hp hRQ x.2 (hTM c.t_mem_T) hx h.orderOf_t
  have hmem : ∀ a : Subgroup.centralizer ({x} : Set d.M),
      g * ((a : d.M) : G) * g⁻¹ ∈ c.T ⊔ c.Q := by
    intro a
    rw [← d.centralizer_t_inf_M hp hRQ hR]
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, d.M.mul_mem (d.M.mul_mem hgM
      (a : d.M).2) (d.M.inv_mem hgM)⟩
    have ha := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp a.2)
    simp only [Subgroup.coe_mul] at ha
    rw [← hg]
    calc g * ((a : d.M) : G) * g⁻¹ * (g * x * g⁻¹) = g * (((a : d.M) : G) * x) * g⁻¹ := by group
      _ = g * (x * ((a : d.M) : G)) * g⁻¹ := by rw [ha]
      _ = g * x * g⁻¹ * (g * ((a : d.M) : G) * g⁻¹) := by group
  refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
  have := T_sup_Q_le_centralizer (c := c) hp (hmem a) (hmem b)
  simp only [Subgroup.coe_mul]
  have h2 := congrArg (fun w => g⁻¹ * w * g) this
  calc ((a : d.M) : G) * ((b : d.M) : G) =
      g⁻¹ * (g * ((a : d.M) : G) * g⁻¹ * (g * ((b : d.M) : G) * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * ((b : d.M) : G) * g⁻¹ * (g * ((a : d.M) : G) * g⁻¹)) * g := h2
    _ = ((b : d.M) : G) * ((a : d.M) : G) := by group

theorem dichotomy
    (hp : h.p ≠ 2) (hS : SuzukiFourGroupTheorem) (hRQ : R ≤ c.Q) (hR : R ≠ ⊥) :
    Subgroup.normalizer (R : Set G) = Subgroup.normalizer (c.T : Set G) ∨
      ∃ L : Subgroup G, Nonempty (L ≃* PSL(2, GaloisField 2 2)) ∧
        IsInternalDirectProduct L c.Q d.M := by
  classical
  have hTM : c.T ≤ d.M := by
    rw [← d.S_inf_eq_T hp hRQ hR]; exact inf_le_right
  rcases hS d.M (d.isKleinFour_sylow hp hRQ) (d.isConj hp hRQ)
    (d.isMulCommutative_centralizer hp hRQ hR) with hn | ⟨L, A, ⟨eL⟩, hAab, hAodd, hLA⟩
  ·
    left
    refine le_antisymm ?_ (c.normalizer_T_le_normalizer_R hp hRQ)
    intro g hg
    set W := c.T.map (MulAut.conj g).toMonoidHom
    have hWM : W ≤ d.M := by
      rintro _ ⟨x, hx, rfl⟩
      exact d.conj_mem hg (hTM hx)
    have hT2 : IsPGroup 2 c.T := IsPGroup.of_card (n := 2) (by rw [c.four.card_four]; norm_num)
    have hW2 : IsPGroup 2 (W.subgroupOf d.M) :=
      (hT2.map (MulAut.conj g).toMonoidHom).of_equiv (Subgroup.subgroupOfEquivOfLe hWM).symm
    obtain ⟨P, hP⟩ := hW2.exists_le_sylow
    have := Sylow.unique_of_normal (d.sylow hp hRQ) (hn _)
    have hPV : P = d.sylow hp hRQ := Subsingleton.elim _ _
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    have h1 : (⟨g * x * g⁻¹, hWM ⟨x, hx, rfl⟩⟩ : d.M) ∈ W.subgroupOf d.M := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨x, hx, rfl⟩
    have h2 := hP h1
    rw [hPV, d.coe_sylow hp hRQ, Subgroup.mem_subgroupOf, d.S_inf_eq_T hp hRQ hR] at h2
    exact h2
  ·
    right
    obtain ⟨hsup, hdisj, hLC⟩ := hLA
    have hLN : L ≤ Subgroup.normalizer (A : Set d.M) :=
      hLC.trans (Subgroup.centralizer_le_normalizer _)
    have hdecomp : ∀ x : d.M, ∃ l ∈ L, ∃ a ∈ A, l * a = x := by
      intro x
      have hx : x ∈ ((L ⊔ A : Subgroup d.M) : Set d.M) := by rw [hsup]; trivial
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLN] at hx
      obtain ⟨l, hl, a, ha, hla⟩ := hx
      exact ⟨l, hl, a, ha, hla⟩
    have hcommLA : ∀ l ∈ L, ∀ a ∈ A, l * a = a * l := fun l hl a ha =>
      ((Subgroup.mem_centralizer_iff.mp (hLC hl)) a ha).symm
    have hLA1 : ∀ z, z ∈ L → z ∈ A → z = 1 := fun z hzL hzA =>
      (Subgroup.disjoint_def.mp hdisj) hzL hzA
    have hpowla : ∀ l ∈ L, ∀ a ∈ A, ∀ n : ℕ, (l * a) ^ n = 1 → l ^ n = 1 ∧ a ^ n = 1 := by
      intro l hl a ha n hn
      rw [(Commute.mul_pow (hcommLA l hl a ha) n)] at hn
      have h1 : l ^ n = (a ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hn
      have h2 : l ^ n = 1 := hLA1 _ (L.pow_mem hl n) (h1 ▸ A.inv_mem (A.pow_mem ha n))
      refine ⟨h2, ?_⟩
      rw [h2, one_mul] at hn
      exact hn
    set t' : d.M := ⟨h.t, hTM c.t_mem_T⟩
    have ht'2 : orderOf t' = 2 := by rw [Subgroup.orderOf_mk, h.orderOf_t]
    have ht'L : t' ∈ L := by
      obtain ⟨l, hl, a, ha, hla⟩ := hdecomp t'
      have ha2 : a ^ 2 = 1 := (hpowla l hl a ha 2 (by rw [hla, ← ht'2, pow_orderOf_eq_one])).2
      have ha1 : a = 1 := by
        have hodd : Odd (orderOf a) := Odd.of_dvd_nat hAodd (Subgroup.orderOf_dvd_natCard A ha)
        have h2 := orderOf_dvd_of_pow_eq_one ha2
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
        · exact orderOf_eq_one_iff.mp h1
        · rw [h1] at hodd; exact absurd hodd (by decide)
      rw [← hla, ha1, mul_one]
      exact hl
    have hQM := d.Q_le hp hRQ
    have hQA : ∀ x (hx : x ∈ c.Q), (⟨x, hQM hx⟩ : d.M) ∈ A := by
      intro x hx
      obtain ⟨l, hl, a, ha, hla⟩ := hdecomp ⟨x, hQM hx⟩
      have hxt : x * h.t = h.t * x := h.commute_of_mem_F (c.toSetup.Q_le_F hp hx)
      have hlt : l * t' = t' * l := by
        have h1 : (l * a) * t' = t' * (l * a) := by
          rw [hla]; exact Subtype.ext hxt
        have hat : a * t' = t' * a := (hcommLA t' ht'L a ha).symm
        have : l * t' * a = t' * l * a := by
          calc l * t' * a = l * (a * t') := by rw [hat, mul_assoc]
            _ = (l * a) * t' := by group
            _ = t' * (l * a) := h1
            _ = t' * l * a := by group
        exact mul_right_cancel this
      have hlodd : Odd (orderOf l) := by
        have hxodd := ((c.toSetup.mem_Q_iff hp).mp hx).2
        have h1 : (l * a) ^ orderOf x = 1 := by
          rw [hla]
          exact Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_orderOf_eq_one x)
        exact Odd.of_dvd_nat hxodd (orderOf_dvd_of_pow_eq_one (hpowla l hl a ha _ h1).1)
      have hl1 : l = 1 := by
        have := eq_one_of_commute_of_psl24 eL (x := ⟨l, hl⟩) (y := ⟨t', ht'L⟩)
          (by rwa [Subgroup.orderOf_mk]) (by rwa [Subgroup.orderOf_mk])
          (Subtype.ext hlt)
        exact congrArg Subtype.val this
      rw [← hla, hl1, one_mul]
      exact ha
    have hAQ : ∀ a ∈ A, ((a : d.M) : G) ∈ c.Q := by
      intro a ha
      have hat : a * t' = t' * a := (hcommLA t' ht'L a ha).symm
      have haTQ : ((a : d.M) : G) ∈ c.T ⊔ c.Q := by
        rw [← d.centralizer_t_inf_M hp hRQ hR]
        exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hat), a.2⟩
      have hTQ : c.T ≤ Subgroup.normalizer (c.Q : Set G) :=
        c.toSetup.T_le_centralizer_Q.trans (Subgroup.centralizer_le_normalizer _)
      have haTQ' := haTQ
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTQ] at haTQ'
      obtain ⟨τ, hτ, q, hq, hτq⟩ := haTQ'
      have hτq : τ * q = ((a : d.M) : G) := hτq
      have hqa : q * ((a : d.M) : G) = ((a : d.M) : G) * q :=
        T_sup_Q_le_centralizer (c := c) hp (Subgroup.mem_sup_right hq) haTQ
      have hτ' : τ = ((a : d.M) : G) * q⁻¹ := by rw [← hτq]; group
      have haodd : Odd (orderOf ((a : d.M) : G)) := by
        rw [Subgroup.orderOf_coe]
        exact Odd.of_dvd_nat hAodd (Subgroup.orderOf_dvd_natCard A ha)
      have hqodd := ((c.toSetup.mem_Q_iff hp).mp hq).2
      have hτn : τ ^ (orderOf ((a : d.M) : G) * orderOf q) = 1 := by
        rw [hτ', (Commute.mul_pow (Commute.inv_right hqa.symm) _), pow_mul, pow_orderOf_eq_one,
          one_pow, one_mul, inv_pow, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow, inv_one]
      have hτodd : Odd (orderOf τ) := Odd.of_dvd_nat (haodd.mul hqodd)
        (orderOf_dvd_of_pow_eq_one hτn)
      have hτ4 : orderOf τ ∣ 4 := c.four.card_four ▸ Subgroup.orderOf_dvd_natCard c.T hτ
      have hτ1 : τ = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left hτ4 (by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
          exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hτodd))) (dvd_refl _))
      rw [← hτq, hτ1, one_mul]
      exact hq
    have hA'Q : A.map d.M.subtype = c.Q := by
      apply le_antisymm
      · rintro _ ⟨a, ha, rfl⟩
        exact hAQ a ha
      · intro x hx
        exact ⟨⟨x, hQM hx⟩, hQA x hx, rfl⟩
    refine ⟨L.map d.M.subtype, ⟨(L.equivMapOfInjective _ d.M.subtype_injective).symm.trans eL⟩,
      ?_, ?_, ?_⟩
    · rw [← hA'Q, ← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    · rw [← hA'Q]
      exact Subgroup.disjoint_map d.M.subtype_injective hdisj
    · rw [← hA'Q]
      rintro _ ⟨l, hl, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp (hLC hl)) a ha)

end IndexTwo

section PSL24Subgroup

variable {X : Type*} [Group X]

theorem eq_one_of_centralizes_psl24 {L : Subgroup X} (eL : L ≃* PSL(2, GaloisField 2 2))
    {z : X} (hzL : z ∈ L) (hz : ∀ y ∈ L, z * y = y * z) : z = 1 := by
  have := isSimpleGroup_of_psl24 eL
  have hnonab : ∃ a b : L, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm : IsMulCommutative L := ⟨⟨hcon⟩⟩
    have hcyc := IsSimpleGroup.isCyclic (α := L)
    have hp := IsSimpleGroup.prime_card (α := L)
    rw [card_of_psl24 eL] at hp
    norm_num at hp
  have := eq_one_of_mem_center_of_isSimpleGroup hnonab (z := ⟨z, hzL⟩)
    (fun y => Subtype.ext (hz y y.2))
  exact congrArg Subtype.val this

theorem le_of_odd_of_psl24 {L Q M K : Subgroup X} (eL : L ≃* PSL(2, GaloisField 2 2))
    (hd : IsInternalDirectProduct L Q M) (hKM : K ≤ M)
    (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) (hKodd : Odd (Nat.card K)) : K ≤ Q := by
  have := isSimpleGroup_of_psl24 eL
  have hLM := hd.left_le
  have hKL : K ⊓ L = ⊥ := by
    have hnorm : ((K ⊓ L).subgroupOf L).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact ⟨hKn _ (hLM g.2) _ hx.1, L.mul_mem (L.mul_mem g.2 hx.2) (L.inv_mem g.2)⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ L).subgroupOf L) with h1 | h1
    · rw [Subgroup.subgroupOf_eq_bot] at h1
      rw [← inf_eq_left.mpr (inf_le_right : K ⊓ L ≤ L), inf_comm]
      exact disjoint_iff.mp h1.symm
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h1
      have h60 : Nat.card L ∣ Nat.card K :=
        Subgroup.card_dvd_of_le (h1.trans inf_le_left)
      rw [card_of_psl24 eL] at h60
      exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr
        ((by norm_num : (2 : ℕ) ∣ 60).trans h60))
  intro k hk
  refine hd.mem_right_of_centralizes (fun z hzL hz => eq_one_of_centralizes_psl24 eL hzL hz)
    (hKM hk) fun y hy => ?_
  have h1 : k * y * k⁻¹ * y⁻¹ ∈ K ⊓ L := by
    refine ⟨?_, L.mul_mem (hd.conj_mem_left (hKM hk) hy) (L.inv_mem hy)⟩
    rw [show k * y * k⁻¹ * y⁻¹ = k * (y * k⁻¹ * y⁻¹) by group]
    exact K.mul_mem hk (hKn _ (hLM hy) _ (K.inv_mem hk))
  rw [hKL, Subgroup.mem_bot] at h1
  calc k * y = (k * y * k⁻¹ * y⁻¹) * y * k := by group
    _ = y * k := by rw [h1, one_mul]

end PSL24Subgroup

namespace Setup

variable {G : Type} [Group G] [Finite G] {h : JTHyp G} (s : Setup h)

theorem lemma_4_3
    (hp : h.p ≠ 2) (hS : SuzukiFourGroupTheorem) {R : Subgroup G}
    (hRQ : R ≤ s.Q) (hR : R ≠ ⊥) :
    Subgroup.normalizer (R : Set G) = Subgroup.normalizer (s.Q : Set G) := by
  obtain ⟨c, rfl⟩ := s.exists_config hp
  have hQR := normalizer_le_normalizer_of_le_isCyclic (c.toSetup.isCyclic_Q hp) hRQ
  obtain ⟨M, hMN, hMn, hMi⟩ := c.exists_index_two hp hRQ hR
  let d : IndexTwo (Subgroup.normalizer (R : Set G)) := ⟨M, hMN, hMn, hMi⟩
  rcases d.dichotomy hp hS hRQ hR with h1 | ⟨L, ⟨eL⟩, hd⟩
  · refine le_antisymm ?_ hQR
    rw [h1]
    exact c.toSetup.normalizer_T_le_normalizer_Q hp
  · refine le_antisymm ?_ hQR
    intro g hg
    have hQab : ∀ x ∈ c.Q, ∀ y ∈ c.Q, x * y = y * x := by
      have := c.toSetup.isCyclic_Q hp
      intro x hx y hy
      exact congrArg Subtype.val ((IsCyclic.commGroup (α := c.Q)).mul_comm ⟨x, hx⟩ ⟨y, hy⟩)
    set K := c.Q.map (MulAut.conj g).toMonoidHom
    have hQM := hd.right_le
    have hKM : K ≤ d.M := by
      rintro _ ⟨x, hx, rfl⟩
      exact d.conj_mem hg (hQM hx)
    have hKn : ∀ m ∈ d.M, ∀ k ∈ K, m * k * m⁻¹ ∈ K := by
      rintro m hm _ ⟨y, hy, rfl⟩
      have hm' : g⁻¹ * m * g ∈ d.M := by
        have := d.conj_mem (Subgroup.inv_mem _ hg) hm
        simpa using this
      refine ⟨(g⁻¹ * m * g) * y * (g⁻¹ * m * g)⁻¹, hd.conj_mem_right hm' hy hQab, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hKodd : Odd (Nat.card K) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact c.toSetup.odd_card_Q hp
    have hKQ := le_of_odd_of_psl24 eL hd hKM hKn hKodd
    refine mem_normalizer_of_conj_mem fun y hy => hKQ ⟨y, hy, rfl⟩

theorem lemma_4_4
    (hp : h.p ≠ 2) (hS : SuzukiFourGroupTheorem) :
    Subgroup.normalizer (s.Q : Set G) = Subgroup.normalizer (s.T : Set G) ∨
      ∃ L D : Subgroup G, Nonempty (L ≃* PSL(2, GaloisField 2 2)) ∧ s.Q ≤ D ∧
        Nonempty (D ≃* DihedralGroup (Nat.card s.Q)) ∧ 2 * (Nat.card D : ℤ) = h.q + h.eps ∧
        IsInternalDirectProduct L D (Subgroup.normalizer (s.Q : Set G)) := by
  classical
  obtain ⟨c, rfl⟩ := s.exists_config hp
  have hQ1 : c.Q ≠ ⊥ := fun h0 => c.toSetup.card_Q_ne_one hp (by rw [h0, Subgroup.card_bot])
  obtain ⟨M, hMN, hMn, hMi⟩ := c.exists_index_two hp le_rfl hQ1
  let d : IndexTwo (Subgroup.normalizer (c.Q : Set G)) := ⟨M, hMN, hMn, hMi⟩
  rcases d.dichotomy hp hS le_rfl hQ1 with h1 | ⟨L, ⟨eL⟩, hd⟩
  · exact Or.inl h1
  right
  have := isSimpleGroup_of_psl24 eL
  have hL60 := card_of_psl24 eL
  have hLM := hd.left_le
  have hQM := hd.right_le
  have hQab : ∀ x ∈ c.Q, ∀ y ∈ c.Q, x * y = y * x := by
    have := c.toSetup.isCyclic_Q hp
    intro x hx y hy
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := c.Q)).mul_comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hZL : ∀ z ∈ L, (∀ y ∈ L, z * y = y * z) → z = 1 := fun z hzL hz =>
    eq_one_of_centralizes_psl24 eL hzL hz
  have hCL : ∀ x ∈ d.M, (∀ y ∈ L, x * y = y * x) → x ∈ c.Q := fun x hx hxL =>
    hd.mem_right_of_centralizes hZL hx hxL
  have hTM : c.T ≤ d.M := by
    rw [← d.S_inf_eq_T hp le_rfl hQ1]; exact inf_le_right
  have huniq : ∀ a ∈ L, ∀ b ∈ c.Q, ∀ a' ∈ L, ∀ b' ∈ c.Q, a * b = a' * b' → a = a' := by
    intro a ha b hb a' ha' b' hb' hab
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [hab]
        _ = b' * b⁻¹ := by group
    have h2 : a'⁻¹ * a = 1 := (Subgroup.disjoint_def.mp hd.2.1) (L.mul_mem (L.inv_mem ha') ha)
      (h1 ▸ c.Q.mul_mem hb' (c.Q.inv_mem hb))
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  have hLnorm : ∀ g ∈ Subgroup.normalizer (c.Q : Set G), ∀ y ∈ L, g * y * g⁻¹ ∈ L := by
    intro g hg
    set L' := L.map (MulAut.conj g).toMonoidHom
    have hL'M : L' ≤ d.M := by
      rintro _ ⟨y, hy, rfl⟩
      exact d.conj_mem hg (hLM hy)
    have hL'n : ∀ m ∈ d.M, ∀ k ∈ L', m * k * m⁻¹ ∈ L' := by
      rintro m hm _ ⟨y, hy, rfl⟩
      have hm' : g⁻¹ * m * g ∈ d.M := by
        have := d.conj_mem (Subgroup.inv_mem _ hg) hm
        simpa using this
      refine ⟨(g⁻¹ * m * g) * y * (g⁻¹ * m * g)⁻¹, hd.conj_mem_left hm' hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hnorm : ((L' ⊓ L).subgroupOf L).Normal := by
      refine ⟨fun x hx l => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact ⟨hL'n _ (hLM l.2) _ hx.1, L.mul_mem (L.mul_mem l.2 hx.2) (L.inv_mem l.2)⟩
    have hLL' : L ≤ L' := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L' ⊓ L).subgroupOf L) with h1 | h1
      · exfalso
        rw [Subgroup.subgroupOf_eq_bot] at h1
        have hL'Q : L' ≤ c.Q := by
          intro k hk
          refine hCL k (hL'M hk) fun y hy => ?_
          have h2 : k * y * k⁻¹ * y⁻¹ ∈ L' ⊓ L := by
            refine ⟨?_, L.mul_mem (hd.conj_mem_left (hL'M hk) hy) (L.inv_mem hy)⟩
            rw [show k * y * k⁻¹ * y⁻¹ = k * (y * k⁻¹ * y⁻¹) by group]
            exact L'.mul_mem hk (hL'n _ (hLM hy) _ (L'.inv_mem hk))
          have h0 : L' ⊓ L = ⊥ := by
            have := disjoint_iff.mp h1
            rwa [inf_eq_left.mpr inf_le_right] at this
          rw [h0, Subgroup.mem_bot] at h2
          calc k * y = (k * y * k⁻¹ * y⁻¹) * y * k := by group
            _ = y * k := by rw [h2, one_mul]
        have h60 : Nat.card L ∣ Nat.card c.Q := by
          have := Subgroup.card_dvd_of_le hL'Q
          rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at this
        rw [hL60] at h60
        exact (Nat.not_even_iff_odd.mpr (c.toSetup.odd_card_Q hp))
          (even_iff_two_dvd.mpr ((by norm_num : (2 : ℕ) ∣ 60).trans h60))
      · rw [Subgroup.subgroupOf_eq_top] at h1
        exact h1.trans inf_le_left
    have hL'L : L' = L := (Subgroup.eq_of_le_of_card_ge hLL' (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])).symm
    intro y hy
    rw [← hL'L]
    exact ⟨y, hy, rfl⟩
  have hpowLQ : ∀ a ∈ L, ∀ b ∈ c.Q, ∀ n : ℕ, (a * b) ^ n = 1 → a ^ n = 1 := by
    intro a ha b hb n hn
    rw [(Commute.mul_pow (hd.commute ha hb) n)] at hn
    have h1 : a ^ n = (b ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hn
    exact (Subgroup.disjoint_def.mp hd.2.1) (L.pow_mem ha n)
      (h1 ▸ c.Q.inv_mem (c.Q.pow_mem hb n))
  have hTL : c.T ≤ L := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hd.exists_mul (hTM hx)
    have hb2 : b ^ 2 = 1 := by
      have hx2 : (a * b) ^ 2 = 1 := by
        rw [pow_two]; exact mul_self_of_isKleinFour' c.four hx
      rw [(Commute.mul_pow (hd.commute ha hb) 2)] at hx2
      have h1 : a ^ 2 = (b ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hx2
      have h2 : a ^ 2 = 1 := (Subgroup.disjoint_def.mp hd.2.1) (L.pow_mem ha 2)
        (h1 ▸ c.Q.inv_mem (c.Q.pow_mem hb 2))
      rw [h2, one_mul] at hx2
      exact hx2
    have hb1 : b = 1 := by
      have hodd := ((c.toSetup.mem_Q_iff hp).mp hb).2
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hb2) with h1 | h1
      · exact orderOf_eq_one_iff.mp h1
      · rw [h1] at hodd; exact absurd hodd (by decide)
    rw [hb1, mul_one]
    exact ha
  have ht₁N : c.t₁ ∈ Subgroup.normalizer (c.Q : Set G) := c.S_le_normalizer_R hp le_rfl c.t₁_mem
  have ht₁M : c.t₁ ∉ d.M := fun h0 => c.t₁_not_mem_T (by
    rw [← d.S_inf_eq_T hp le_rfl hQ1]; exact ⟨c.t₁_mem, h0⟩)
  have hμM := d.μ_mem hp le_rfl
  obtain ⟨l₀, hl₀, q₀, hq₀, hμ⟩ := hd.exists_mul hμM
  have hq₀T : ∀ x ∈ c.T, q₀ * x = x * q₀ := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (c.toSetup.T_le_centralizer_Q hx) q₀ hq₀)
  have hl₀3 : orderOf l₀ = 3 := by
    refine orderOf_eq_prime (hpowLQ l₀ hl₀ q₀ hq₀ 3 (by rw [hμ, ← c.orderOf_μ,
      pow_orderOf_eq_one])) ?_
    intro h1
    rw [h1, one_mul] at hμ
    have : Nontrivial c.T := by
      rw [← Finite.one_lt_card_iff_nontrivial, c.four.card_four]; norm_num
    obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : c.T)
    apply hx1
    apply Subtype.ext
    apply c.μ_fpf x hx
    rw [← hμ, hq₀T x hx, mul_inv_cancel_right]
  have hl₀T : ∀ x ∈ c.T, l₀ * x * l₀⁻¹ ∈ c.T := by
    intro x hx
    have : l₀ * x * l₀⁻¹ = c.μ * x * c.μ⁻¹ := by
      rw [← hμ, show l₀ * q₀ * x * (l₀ * q₀)⁻¹ = l₀ * (q₀ * x) * q₀⁻¹ * l₀⁻¹ by group,
        hq₀T x hx]
      group
    rw [this]
    exact (Subgroup.mem_normalizer_iff.mp c.μ_mem_NT x).mp hx
  have ht₁l₀ : c.t₁ * l₀ * c.t₁⁻¹ = l₀ := by
    have h1 : c.t₁ * c.μ * c.t₁⁻¹ = c.μ := by rw [← c.comm, mul_inv_cancel_right]
    rw [← hμ, show c.t₁ * (l₀ * q₀) * c.t₁⁻¹ = (c.t₁ * l₀ * c.t₁⁻¹) * (c.t₁ * q₀ * c.t₁⁻¹) by
      group] at h1
    exact huniq _ (hLnorm _ ht₁N _ hl₀) _ ((Subgroup.mem_normalizer_iff.mp ht₁N q₀).mp hq₀) l₀
      hl₀ q₀ hq₀ h1
  have hab := h.abelian_sylow c.S
  have ht₁T : ∀ x ∈ c.T, c.t₁ * x * c.t₁⁻¹ = x := fun x hx => by
    have hc : c.t₁ * x = x * c.t₁ :=
      congrArg Subtype.val (hab.is_comm.comm ⟨c.t₁, c.t₁_mem⟩ ⟨x, c.le_S hx⟩)
    rw [hc, mul_inv_cancel_right]
  let σ : MulAut L :=
    { toFun := fun y => ⟨c.t₁ * y * c.t₁⁻¹, hLnorm _ ht₁N _ y.2⟩
      invFun := fun y => ⟨c.t₁⁻¹ * y * c.t₁, by
        have := hLnorm _ (Subgroup.inv_mem _ ht₁N) _ y.2
        simpa using this⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hTcard : Nat.card (c.T.subgroupOf L) = 2 ^ (Nat.card L).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv, c.four.card_four, hL60,
      show (60 : ℕ) = 2 ^ 2 * 15 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simp
  let T' : Sylow 2 L := Sylow.ofCard (c.T.subgroupOf L) hTcard
  have hσ1 := eq_one_of_mulAut_of_psl24 eL T' (l := ⟨l₀, hl₀⟩) (by rwa [Subgroup.orderOf_mk])
    (mem_normalizer_of_conj_mem fun x hx => by
      change (x : G) ∈ c.T at hx
      change (l₀ * (x : G) * l₀⁻¹) ∈ c.T
      exact hl₀T _ hx) σ
    (fun x hx => Subtype.ext (by
      change (x : G) ∈ c.T at hx
      exact ht₁T _ hx))
    (Subtype.ext ht₁l₀)
  have ht₁C : c.t₁ ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := congrArg Subtype.val (DFunLike.congr_fun hσ1 ⟨y, hy⟩)
    change c.t₁ * y * c.t₁⁻¹ = y at this
    calc y * c.t₁ = (c.t₁ * y * c.t₁⁻¹) * c.t₁ := by rw [this]
      _ = c.t₁ * y := by group
  set D := Subgroup.centralizer (L : Set G) ⊓ Subgroup.normalizer (c.Q : Set G)
  have hQC : c.Q ≤ Subgroup.centralizer (L : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hd.commute hy hx
  have hQD : c.Q ≤ D := le_inf hQC Subgroup.le_normalizer
  have ht₁D : c.t₁ ∈ D := ⟨ht₁C, ht₁N⟩
  have hDM : ∀ x ∈ D, x ∈ d.M → x ∈ c.Q := fun x hx hxM =>
    hCL x hxM fun y hy => ((Subgroup.mem_centralizer_iff.mp hx.1) y hy).symm
  have hmulM := fun {a b : G} (ha : a ∈ Subgroup.normalizer (c.Q : Set G))
      (hb : b ∈ Subgroup.normalizer (c.Q : Set G)) => mul_mem_iff_of_relIndex_two d.index ha hb
  have hDcard : Nat.card D = 2 * Nat.card c.Q := by
    refine card_eq_two_mul_of_xor hQD ht₁D fun b hb => ⟨fun hbt hbQ => ?_, fun hbQ => ?_⟩
    · have : c.t₁ ∈ c.Q := by
        have : c.t₁ = b⁻¹ * (b * c.t₁) := by group
        rw [this]
        exact c.Q.mul_mem (c.Q.inv_mem hbQ) hbt
      have hodd := ((c.toSetup.mem_Q_iff hp).mp this).2
      rw [c.orderOf_t₁] at hodd
      exact absurd hodd (by decide)
    · have hbM : b ∉ d.M := fun h1 => hbQ (hDM b hb h1)
      have hbt : b * c.t₁ ∈ d.M := (hmulM hb.2 ht₁N).mpr ⟨fun h1 => absurd h1 hbM,
        fun h1 => absurd h1 ht₁M⟩
      exact hDM _ (D.mul_mem hb ht₁D) hbt
  have hinv : ∀ x ∈ c.Q, c.t₁ * x * c.t₁⁻¹ = x⁻¹ := fun x hx =>
    c.toSetup.conj_eq_inv_of_mem_S hp c.t₁_mem c.t₁_not_mem_T hx
  have ht₁Q : c.t₁ ∉ c.Q := fun h1 => by
    have hodd := ((c.toSetup.mem_Q_iff hp).mp h1).2
    rw [c.orderOf_t₁] at hodd
    exact absurd hodd (by decide)
  have ht₁t₁ : c.t₁ * c.t₁ = 1 := by rw [← pow_two, ← c.orderOf_t₁, pow_orderOf_eq_one]
  have hDeq : c.Q ⊔ Subgroup.zpowers c.t₁ = D := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hQD ((Subgroup.zpowers_le).mpr ht₁D))
    rw [hDcard]
    have h1 : Nat.card c.Q ∣ Nat.card (c.Q ⊔ Subgroup.zpowers c.t₁ : Subgroup G) :=
      Subgroup.card_dvd_of_le le_sup_left
    have h2 : 2 ∣ Nat.card (c.Q ⊔ Subgroup.zpowers c.t₁ : Subgroup G) := by
      rw [← c.orderOf_t₁, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le le_sup_right
    have hcop : Nat.Coprime 2 (Nat.card c.Q) := Nat.coprime_two_left.mpr (c.toSetup.odd_card_Q hp)
    exact Nat.le_of_dvd Nat.card_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 h1)
  have hdih := nonempty_sup_zpowers_mulEquiv_dihedralGroup c.Q (c.toSetup.isCyclic_Q hp) c.t₁
    ht₁Q ht₁t₁ hinv
  rw [hDeq] at hdih
  refine ⟨L, D, ⟨eL⟩, hQD, hdih, ?_, ?_, ?_, ?_⟩
  · rw [hDcard]
    push_cast
    linarith [c.toSetup.four_mul_card_Q hp]
  ·
    apply le_antisymm (sup_le (hLM.trans d.le) inf_le_right)
    intro x hx
    by_cases hxM : x ∈ d.M
    · rw [← hd.1] at hxM
      exact (sup_le_sup_left hQD L) hxM
    · have hxt : x * c.t₁ ∈ d.M := (hmulM hx ht₁N).mpr ⟨fun h1 => absurd h1 hxM,
        fun h1 => absurd h1 ht₁M⟩
      have : x = (x * c.t₁) * c.t₁⁻¹ := by group
      rw [this]
      refine Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_right (D.inv_mem ht₁D))
      rw [← hd.1] at hxt
      exact (sup_le_sup_left hQD L) hxt
  · rw [Subgroup.disjoint_def]
    intro z hzL hzD
    exact hZL z hzL fun y hy => ((Subgroup.mem_centralizer_iff.mp hzD.1) y hy).symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp hy.1) x hx).symm



end Setup

end CFSG.Walter.JT
