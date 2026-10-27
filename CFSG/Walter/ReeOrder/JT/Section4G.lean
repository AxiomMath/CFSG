module

public import CFSG.Walter.ReeOrder.JT.Section4F

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups

theorem card_sup_eq_mul_of_disjoint {X : Type*} [Group X] [Finite X] {H K : Subgroup X}
    (hHK : H ≤ Subgroup.normalizer (K : Set X)) (hdisj : Disjoint H K) :
    Nat.card (H ⊔ K : Subgroup X) = Nat.card H * Nat.card K := by
  classical
  let φ : H × K → (H ⊔ K : Subgroup X) := fun p =>
    ⟨(p.1 : X) * p.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2)⟩
  have hφi : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h1 : (a : X) * b = a' * b' := congrArg Subtype.val hab
    have h2 : (a' : X)⁻¹ * a = b' * (b : X)⁻¹ := by
      calc (a' : X)⁻¹ * a = (a' : X)⁻¹ * (a * b) * (b : X)⁻¹ := by group
        _ = (a' : X)⁻¹ * (a' * b') * (b : X)⁻¹ := by rw [h1]
        _ = b' * (b : X)⁻¹ := by group
    have h3 : (a' : X)⁻¹ * a = 1 := (Subgroup.disjoint_def.mp hdisj)
      (H.mul_mem (H.inv_mem a'.2) a.2) (h2 ▸ K.mul_mem b'.2 (K.inv_mem b.2))
    have ha : (a : X) = a' := by
      calc (a : X) = a' * ((a' : X)⁻¹ * a) := by group
        _ = a' := by rw [h3, mul_one]
    have hb : (b : X) = b' := by
      calc (b : X) = (a : X)⁻¹ * (a * b) := by group
        _ = (a : X)⁻¹ * (a' * b') := by rw [h1]
        _ = b' := by rw [ha]; group
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHK] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hφi, hφs⟩)).symm

namespace Setup

variable {G : Type} [Group G] [Finite G] {h : JTHyp G} (s : Setup h) (hp : h.p ≠ 2)
  (hS : SuzukiFourGroupTheorem)
include hp hS

omit hS in
theorem mem_Q_of_mem_D
    {D : Subgroup G} (hQD : s.Q ≤ D)
    (hD : 2 * (Nat.card D : ℤ) = h.q + h.eps) {x : G} (hx : x ∈ D) (hodd : Odd (orderOf x)) :
    x ∈ s.Q := by
  have h4 := s.four_mul_card_Q hp
  have hDcard : Nat.card D = 2 * Nat.card s.Q := by
    have : (Nat.card D : ℤ) = 2 * Nat.card s.Q := by linarith
    exact_mod_cast this
  have hidx : (s.Q.subgroupOf D).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card s.Q D
    rw [inf_eq_left.mpr hQD, hDcard] at h1
    have hpos : 0 < Nat.card s.Q := Nat.card_pos
    rw [← Subgroup.relIndex]
    nlinarith
  exact mem_of_relIndex_two_of_odd hidx hx hodd

theorem card_normalizer_Q :
    Nat.card (Subgroup.normalizer (s.Q : Set G)) = 24 * Nat.card s.Q ∨
      Nat.card (Subgroup.normalizer (s.Q : Set G)) = 120 * Nat.card s.Q := by
  rcases s.lemma_4_4 hp hS with h1 | ⟨L, D, ⟨eL⟩, hQD, -, hD, hLD⟩
  · left
    rw [h1]
    have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (s.T : Set G))
      (Subgroup.normalizer (s.T : Set G))
    rw [s.relIndex_centralizer_T_normalizer_T hp, inf_eq_left.mpr
      s.centralizer_T_le_normalizer_T, s.card_centralizer_T hp] at h2
    omega
  · right
    have h4 := s.four_mul_card_Q hp
    have hDcard : Nat.card D = 2 * Nat.card s.Q := by
      have : (Nat.card D : ℤ) = 2 * Nat.card s.Q := by linarith
      exact_mod_cast this
    rw [← hLD.1, sup_comm, card_sup_eq_mul_of_disjoint
      (fun x hx => Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun y hy => hLD.commute hy hx))
      hLD.2.1.symm, card_of_psl24 eL, hDcard]
    ring

theorem le_Q_of_normal_of_odd
    {K : Subgroup G} (hKN : K ≤ Subgroup.normalizer (s.Q : Set G))
    (hKn : ∀ g ∈ Subgroup.normalizer (s.Q : Set G), ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hKodd : Odd (Nat.card K)) : K ≤ s.Q := by
  rcases s.lemma_4_4 hp hS with h1 | ⟨L, D, ⟨eL⟩, hQD, -, hD, hLD⟩
  · intro k hk
    have hkN : k ∈ Subgroup.normalizer (s.T : Set G) := h1 ▸ hKN hk
    refine (s.mem_Q_iff hp).mpr ⟨Subgroup.mem_centralizer_iff.mpr fun x hx => ?_,
      Odd.of_dvd_nat hKodd (Subgroup.orderOf_dvd_natCard K hk)⟩
    have hxN : x ∈ Subgroup.normalizer (s.Q : Set G) :=
      h1 ▸ s.centralizer_T_le_normalizer_T (s.S_le_centralizer_T (s.le_S hx))
    set z := x * k * x⁻¹ * k⁻¹
    have hzK : z ∈ K := K.mul_mem (hKn x hxN k hk) (K.inv_mem hk)
    have hzT : z ∈ s.T := by
      rw [show z = x * (k * x⁻¹ * k⁻¹) by simp only [z]; group]
      exact s.T.mul_mem hx ((Subgroup.mem_normalizer_iff.mp hkN _).mp (s.T.inv_mem hx))
    have hz1 : z = 1 := by
      have ho := Odd.of_dvd_nat hKodd (Subgroup.orderOf_dvd_natCard K hzK)
      have h4 : orderOf z ∣ 4 := s.four.card_four ▸ Subgroup.orderOf_dvd_natCard s.T hzT
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h4
        (by rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
            exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr ho))) (dvd_refl _))
    calc x * k = (x * k * x⁻¹ * k⁻¹) * k * x := by group
      _ = k * x := by rw [show x * k * x⁻¹ * k⁻¹ = z from rfl, hz1, one_mul]
  · have hKD := le_of_odd_of_psl24 eL hLD hKN hKn hKodd
    exact fun k hk => s.mem_Q_of_mem_D hp hQD hD (hKD hk)
      (Odd.of_dvd_nat hKodd (Subgroup.orderOf_dvd_natCard K hk))

theorem mem_centralizer_Q_of_coprime
    {y : G} (hy : y ∈ Subgroup.normalizer (s.Q : Set G))
    (hcop : Nat.Coprime (orderOf y) 6) : y ∈ Subgroup.centralizer (s.Q : Set G) := by
  have hQab : ∀ x ∈ s.Q, ∀ z ∈ s.Q, x * z = z * x := by
    have := s.isCyclic_Q hp
    intro x hx z hz
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := s.Q)).mul_comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hQC : s.Q ≤ Subgroup.centralizer (s.Q : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun z hz => hQab z hz x hx
  have hodd : Odd (orderOf y) := Nat.coprime_two_right.mp
    (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hcop)
  rcases s.lemma_4_4 hp hS with h1 | ⟨L, D, ⟨eL⟩, hQD, -, hD, hLD⟩
  ·
    have hyT : y ∈ Subgroup.normalizer (s.T : Set G) := h1 ▸ hy
    have h3 : y ^ 3 ∈ Subgroup.centralizer (s.T : Set G) := by
      have := centralizer_subgroupOf_normalizer_normal s.T
      have h2 := Subgroup.pow_index_mem ((Subgroup.centralizer (s.T : Set G)).subgroupOf
        (Subgroup.normalizer (s.T : Set G))) (⟨y, hyT⟩ : Subgroup.normalizer (s.T : Set G))
      rw [← Subgroup.relIndex, s.relIndex_centralizer_T_normalizer_T hp,
        Subgroup.mem_subgroupOf] at h2
      exact h2
    have hcop3 : Nat.Coprime (orderOf y) 3 :=
      Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hcop
    have hyC : y ∈ Subgroup.centralizer (s.T : Set G) := by
      have heq : Subgroup.zpowers (y ^ 3) = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr
          (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) 3))
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hcop3.orderOf_pow])
      have : y ∈ Subgroup.zpowers (y ^ 3) := heq ▸ Subgroup.mem_zpowers y
      exact ((Subgroup.zpowers_le).mpr h3) this
    exact hQC ((s.mem_Q_iff hp).mpr ⟨hyC, hodd⟩)
  · obtain ⟨l, hl, d, hd, rfl⟩ := hLD.exists_mul hy
    have hn := pow_orderOf_eq_one (l * d)
    rw [Commute.mul_pow (hLD.commute hl hd)] at hn
    have hl' : l ^ orderOf (l * d) = (d ^ orderOf (l * d))⁻¹ := eq_inv_of_mul_eq_one_left hn
    have hl1 : l ^ orderOf (l * d) = 1 := (Subgroup.disjoint_def.mp hLD.2.1)
      (L.pow_mem hl _) (hl' ▸ D.inv_mem (D.pow_mem hd _))
    rw [hl1, one_mul] at hn
    have hdQ : d ∈ s.Q := s.mem_Q_of_mem_D hp hQD hD hd
      (Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hn))
    refine Subgroup.mul_mem _ ?_ (hQC hdQ)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hLD.commute hl (hQD hx)).symm

theorem eq_of_inf_ne_bot (g : G)
    (hne : s.Q ⊓ s.Q.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    s.Q.map (MulAut.conj g).toMonoidHom = s.Q := by
  obtain ⟨⟨z, hzQ, hzQ'⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz1' : z ≠ 1 := fun h0 => hz1 (Subtype.ext h0)
  obtain ⟨z', hz'Q, rfl⟩ := hzQ'
  have hz'1 : z' ≠ 1 := fun h0 => hz1' (by simp [h0])
  have hR1 : Subgroup.zpowers (MulAut.conj g z') ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]; exact hz1'
  have hR2 : Subgroup.zpowers z' ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]; exact hz'1
  have hN1 := s.lemma_4_3 hp hS ((Subgroup.zpowers_le).mpr hzQ) hR1
  have hN2 := s.lemma_4_3 hp hS ((Subgroup.zpowers_le).mpr hz'Q) hR2
  have hNN : Subgroup.normalizer (s.Q : Set G) =
      Subgroup.normalizer ((s.Q.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [← hN1, ← Subgroup.map_equiv_normalizer_eq, ← hN2, Subgroup.map_equiv_normalizer_eq,
      MonoidHom.map_zpowers]
  have hle := s.le_Q_of_normal_of_odd hp hS (K := s.Q.map (MulAut.conj g).toMonoidHom)
    (hNN ▸ Subgroup.le_normalizer)
    (fun x hx k hk => by
      rw [hNN] at hx
      exact (Subgroup.mem_normalizer_iff.mp hx k).mp hk)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact s.odd_card_Q hp)
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

end Setup

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp : h.p ≠ 2)
include hp

theorem exists_conj_zpowers_of_orderOf_three
    (h3 : h.p ≠ 3) {x y u v : G} (hx : orderOf x = 3)
    (hy : orderOf y = 3) (hu : orderOf u = 2) (hv : orderOf v = 2) (hxu : x * u = u * x)
    (hyv : y * v = v * y) :
    ∃ g : G, (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x := by
  classical
  have hF := h.facts hp
  have hinF : ∀ {w e : G}, orderOf w = 3 → orderOf e = 2 → w * e = e * w →
      ∃ a : G, a * w * a⁻¹ ∈ h.F := by
    intro w e hw he hwe
    obtain ⟨a, ha⟩ := h.exists_conj_eq_t hp he
    refine ⟨a, h.mem_F_of_odd (Subgroup.mem_centralizer_singleton_iff.mpr ?_) ?_⟩
    · rw [← ha]
      calc a * w * a⁻¹ * (a * e * a⁻¹) = a * (w * e) * a⁻¹ := by group
        _ = a * (e * w) * a⁻¹ := by rw [hwe]
        _ = a * e * a⁻¹ * (a * w * a⁻¹) := by group
    · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hw]; decide
  obtain ⟨a, haF⟩ := hinF hx hu hxu
  obtain ⟨b, hbF⟩ := hinF hy hv hyv
  set x' := a * x * a⁻¹
  set y' := b * y * b⁻¹
  have hx' : orderOf x' = 3 := by
    simp only [x']; rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
  have hy' : orderOf y' = 3 := by
    simp only [y']; rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hX : IsPGroup 3 (Subgroup.zpowers (⟨x', haF⟩ : h.F)) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx', pow_one])
  have hY : IsPGroup 3 (Subgroup.zpowers (⟨y', hbF⟩ : h.F)) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hy', pow_one])
  obtain ⟨P₁, hP₁⟩ := hX.exists_le_sylow
  obtain ⟨P₂, hP₂⟩ := hY.exists_le_sylow
  obtain ⟨f, hf⟩ := MulAction.exists_smul_eq h.F P₂ P₁
  have hcyc : IsCyclic (P₁ : Subgroup h.F) := by
    have := hF.cyclic 3 (by norm_num) (by norm_num) (fun h0 => h3 h0.symm)
      ((P₁ : Subgroup h.F).map h.F.subtype) (Subgroup.map_subtype_le _) (P₁.isPGroup'.map _)
    exact isCyclic_of_surjective ((P₁ : Subgroup h.F).equivMapOfInjective _
      h.F.subtype_injective).symm (MulEquiv.surjective _)
  have hfy : f * ⟨y', hbF⟩ * f⁻¹ ∈ (P₁ : Subgroup h.F) := by
    rw [← hf]
    change f * ⟨y', hbF⟩ * f⁻¹ ∈ MulAut.conj f • (P₂ : Subgroup h.F)
    exact ⟨_, hP₂ (Subgroup.mem_zpowers _), rfl⟩
  have hxP : (⟨x', haF⟩ : h.F) ∈ (P₁ : Subgroup h.F) := hP₁ (Subgroup.mem_zpowers _)
  have heq : Subgroup.zpowers (⟨f * ⟨y', hbF⟩ * f⁻¹, hfy⟩ : (P₁ : Subgroup h.F)) =
      Subgroup.zpowers ⟨⟨x', haF⟩, hxP⟩ := by
    refine IsCyclic.subgroup_eq_iff_card_eq.mpr ?_
    have hl : orderOf (⟨f * ⟨y', hbF⟩ * f⁻¹, hfy⟩ : (P₁ : Subgroup h.F)) = 3 := by
      rw [Subgroup.orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy']
    have hr : orderOf (⟨⟨x', haF⟩, hxP⟩ : (P₁ : Subgroup h.F)) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hx']
    rw [Nat.card_zpowers, Nat.card_zpowers, hl, hr]
  refine ⟨a⁻¹ * (f : G) * b, ?_⟩
  rw [MonoidHom.map_zpowers]
  have h1 : (MulAut.conj (a⁻¹ * (f : G) * b)).toMonoidHom y =
      a⁻¹ * ((f : G) * y' * (f : G)⁻¹) * a := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, y']
    group
  rw [h1]
  have h2 := congrArg (fun H => (H.map (P₁ : Subgroup h.F).subtype).map h.F.subtype) heq
  simp only [MonoidHom.map_zpowers] at h2
  change Subgroup.zpowers ((f : G) * y' * (f : G)⁻¹) = Subgroup.zpowers x' at h2
  have h3 := congrArg (fun H => H.map (MulAut.conj a⁻¹).toMonoidHom) h2
  simp only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h3
  rw [h3]
  congr 1
  simp only [x']
  group

end JTHyp

end CFSG.Walter.JT
