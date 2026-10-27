module

public import CFSG.Walter.J1.Seven

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem exists_mul_of_involution {x t : G} (hx1 : x ≠ 1) (hx : Nat.Coprime (orderOf x) 30)
    (ht : orderOf t = 2) (htx : t * x * t⁻¹ = x⁻¹) {w : G} (hw : orderOf w = 2)
    (hwN : w ∈ Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G) : Subgroup G) :
      Set G)) :
    w * t ∈ Subgroup.centralizer ({x} : Set G) := by
  set A := Subgroup.centralizer ({x} : Set G)
  have hw2 := (orderOf_eq_two_iff.mp hw).1
  have hwinv : ∀ a ∈ A, w * a * w⁻¹ = a⁻¹ :=
    inv_of_inf_centralizer_eq_bot hw2 hwN (by
      rw [inf_comm]
      rw [eq_bot_iff]
      intro z ⟨hzw, hzx⟩
      have := h.inf_centralizer_eq_bot hx1 hx hw
      rw [eq_bot_iff] at this
      exact this ⟨hzx, hzw⟩)
  have htinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹ := h.inv_of_mem_centralizer hx1 hx ht htx
  have h1 : w * t * x * (w * t)⁻¹ = x := by
    rw [mul_inv_rev, show w * t * x * (t⁻¹ * w⁻¹) = w * (t * x * t⁻¹) * w⁻¹ by group,
      htinv x (Subgroup.mem_centralizer_singleton_iff.mpr rfl),
      show w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ by group,
      hwinv x (Subgroup.mem_centralizer_singleton_iff.mpr rfl), inv_inv]
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc w * t * x = w * t * x * (w * t)⁻¹ * (w * t) := by group
    _ = x * (w * t) := by rw [h1]

include h in
theorem exists_mem_centralizer_of_mem_normalizer {x t : G} (hx1 : x ≠ 1)
    (hx : Nat.Coprime (orderOf x) 30) (ht : orderOf t = 2) (htx : t * x * t⁻¹ = x⁻¹) {g : G}
    (hg : g ∈ Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G) : Subgroup G) :
      Set G)) :
    ∃ b ∈ Subgroup.centralizer ({x} : Set G), b⁻¹ * g ∈ Subgroup.centralizer ({t} : Set G) := by
  set A := Subgroup.centralizer ({x} : Set G)
  have ht2 := (orderOf_eq_two_iff.mp ht).1
  have htinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹ := h.inv_of_mem_centralizer hx1 hx ht htx
  have htN : t ∈ Subgroup.normalizer (A : Set G) :=
    mem_normalizer_of_conj_mem fun a ha => by rw [htinv a ha]; exact A.inv_mem ha
  have hw : orderOf (g * t * g⁻¹) = 2 := by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
  have hwN : g * t * g⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg htN) (Subgroup.inv_mem _ hg)
  have ha := h.exists_mul_of_involution hx1 hx ht htx hw hwN
  set a := g * t * g⁻¹ * t
  have hodd : Odd (Nat.card A) := by
    have hc := h.coprime_card_centralizer hx1 hx
    rw [Nat.odd_iff]
    by_contra h0
    have h2 : 2 ∣ Nat.card A := Nat.dvd_of_mod_eq_zero (by omega)
    have := Nat.dvd_gcd h2 (by norm_num : 2 ∣ 30)
    rw [hc] at this
    norm_num at this
  obtain ⟨j, hj⟩ := hodd
  set b := a ^ (j + 1)
  have hbA : b ∈ A := A.pow_mem ha _
  have hb2 : b * b = a := by
    rw [← pow_two, ← pow_mul, show (j + 1) * 2 = Nat.card A + 1 by omega, pow_succ,
      pow_card_eq_one_of_mem ha, one_mul]
  refine ⟨b, hbA, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hbt : b * t * b⁻¹ = g * t * g⁻¹ := by
    have h1 : t * b⁻¹ * t⁻¹ = b := by rw [htinv _ (A.inv_mem hbA), inv_inv]
    calc b * t * b⁻¹ = b * (t * b⁻¹ * t⁻¹) * t := by group
      _ = b * b * t := by rw [h1]
      _ = a * t := by rw [hb2]
      _ = g * t * g⁻¹ := by simp only [a]; rw [mul_assoc, ht2, mul_one]
  calc b⁻¹ * g * t = b⁻¹ * (g * t * g⁻¹) * g := by group
    _ = b⁻¹ * (b * t * b⁻¹) * g := by rw [hbt]
    _ = t * (b⁻¹ * g) := by group

include h in
theorem card_normalizer_eq {x t : G} (hx1 : x ≠ 1) (hx : Nat.Coprime (orderOf x) 30)
    (ht : orderOf t = 2) (htx : t * x * t⁻¹ = x⁻¹) :
    Nat.card (Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) *
        Nat.card (Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G) : Subgroup G) :
          Set G) ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
  set A := Subgroup.centralizer ({x} : Set G)
  set N := Subgroup.normalizer (A : Set G)
  set L := N ⊓ Subgroup.centralizer ({t} : Set G)
  have hbot := h.inf_centralizer_eq_bot hx1 hx ht
  let φ : A × L → N := fun p => ⟨p.1 * p.2, N.mul_mem (Subgroup.le_normalizer p.1.2) p.2.2.1⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨a, l⟩ ⟨a', l'⟩ hal
      have h1 : (a : G) * l = a' * l' := congrArg Subtype.val hal
      have h2 : (a' : G)⁻¹ * a = l' * (l : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * l) * (l : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * l') * (l : G)⁻¹ := by rw [h1]
          _ = l' * (l : G)⁻¹ := by group
      have h3 : (a' : G)⁻¹ * a ∈ A ⊓ Subgroup.centralizer ({t} : Set G) :=
        ⟨A.mul_mem (A.inv_mem a'.2) a.2, h2 ▸ Subgroup.mul_mem _ l'.2.2
          (Subgroup.inv_mem _ l.2.2)⟩
      rw [hbot, Subgroup.mem_bot] at h3
      have h4 : (a : G) = a' := by
        calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
          _ = a' := by rw [h3, mul_one]
      have h5 : (l : G) = l' := by
        rw [h4] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
    · rintro ⟨g, hg⟩
      obtain ⟨b, hbA, hbg⟩ := h.exists_mem_centralizer_of_mem_normalizer hx1 hx ht htx hg
      refine ⟨⟨⟨b, hbA⟩, ⟨b⁻¹ * g, N.mul_mem (N.inv_mem (Subgroup.le_normalizer hbA)) hg,
        hbg⟩⟩, ?_⟩
      apply Subtype.ext
      change b * (b⁻¹ * g) = g
      group
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod]

include h in
theorem mem_of_mem_normalizer {x t : G} (hx1 : x ≠ 1) (hx : Nat.Coprime (orderOf x) 30)
    (ht : orderOf t = 2) (htx : t * x * t⁻¹ = x⁻¹) {z : G}
    (hz : z ∈ Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G))
    (hzc : Nat.Coprime (orderOf z) 120) : z ∈ Subgroup.centralizer ({x} : Set G) := by
  set A := Subgroup.centralizer ({x} : Set G)
  set N := Subgroup.normalizer (A : Set G)
  obtain ⟨b, hbA, hl⟩ := h.exists_mem_centralizer_of_mem_normalizer hx1 hx ht htx hz
  set l := b⁻¹ * z
  have hlN : l ∈ N := N.mul_mem (N.inv_mem (Subgroup.le_normalizer hbA)) hz
  have hzl : z = b * l := by simp only [l]; group
  have hpow : ∀ n : ℕ, ∃ c ∈ A, (b * l) ^ n = c * l ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, A.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨c, hc, hcn⟩ := ih
      have hlnN : l ^ n ∈ N := N.pow_mem hlN n
      refine ⟨c * (l ^ n * b * (l ^ n)⁻¹), A.mul_mem hc
        ((Subgroup.mem_normalizer_iff.mp hlnN b).mp hbA), ?_⟩
      rw [pow_succ, hcn]
      group
  obtain ⟨c, hc, hcn⟩ := hpow (orderOf z)
  rw [← hzl, pow_orderOf_eq_one] at hcn
  have hln : l ^ orderOf z = c⁻¹ := by
    calc l ^ orderOf z = c⁻¹ * (c * l ^ orderOf z) := by group
      _ = c⁻¹ := by rw [← hcn, mul_one]
  have hln1 : l ^ orderOf z = 1 := by
    have hmem : l ^ orderOf z ∈ A ⊓ Subgroup.centralizer ({t} : Set G) :=
      ⟨hln ▸ A.inv_mem hc, Subgroup.pow_mem _ hl _⟩
    rw [h.inf_centralizer_eq_bot hx1 hx ht, Subgroup.mem_bot] at hmem
    exact hmem
  have hl120 : orderOf l ∣ 120 := by
    rw [← h.card_centralizer_involution ht, ← Subgroup.orderOf_mk l hl]
    exact orderOf_dvd_natCard _
  have hl1 : l = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hzc (orderOf_dvd_of_pow_eq_one hln1) hl120)
  rw [hzl, hl1, mul_one]
  exact hbA

include h in
theorem eq_one_of_conj_mem_normalizer {x t : G} (hx1 : x ≠ 1) (hx : Nat.Coprime (orderOf x) 30)
    (ht : orderOf t = 2) (htx : t * x * t⁻¹ = x⁻¹) {g a : G}
    (hg : g ∉ Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G))
    (ha : a ∈ Subgroup.centralizer ({x} : Set G))
    (hga : g⁻¹ * a * g ∈ Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G) :
      Subgroup G) : Set G)) : a = 1 := by
  set A := Subgroup.centralizer ({x} : Set G)
  by_contra ha1
  have hac : Nat.Coprime (orderOf a) 30 := by
    have h1 : orderOf a ∣ Nat.card A := by
      rw [← Subgroup.orderOf_mk a ha]
      exact orderOf_dvd_natCard _
    exact Nat.Coprime.coprime_dvd_left h1 (h.coprime_card_centralizer hx1 hx)
  have hzc : Nat.Coprime (orderOf (g⁻¹ * a * g)) 120 := by
    rw [show g⁻¹ * a * g = g⁻¹ * a * g⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      MulEquiv.orderOf_eq]
    exact coprime_of_coprime_thirty hac
  have hzA := h.mem_of_mem_normalizer hx1 hx ht htx hga hzc
  have hz1 : g⁻¹ * a * g ≠ 1 := by
    intro h1
    apply ha1
    calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hCz := h.centralizer_eq_of_mem hx1 hx ht htx hzA hz1
  have hCa := h.centralizer_eq_of_mem hx1 hx ht htx ha ha1
  apply hg
  have hginv : g⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
    refine mem_normalizer_of_conj_mem fun w hw => ?_
    rw [inv_inv]
    have hwa : w ∈ Subgroup.centralizer ({a} : Set G) := hCa ▸ hw
    change g⁻¹ * w * g ∈ Subgroup.centralizer ({x} : Set G)
    rw [← hCz, Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp hwa
    calc g⁻¹ * w * g * (g⁻¹ * a * g) = g⁻¹ * (w * a) * g := by group
      _ = g⁻¹ * (a * w) * g := by rw [this]
      _ = g⁻¹ * a * g * (g⁻¹ * w * g) := by group
  simpa using Subgroup.inv_mem _ hginv

include h in
theorem dvd_index_sub_one {x t : G} (hx1 : x ≠ 1) (hx : Nat.Coprime (orderOf x) 30)
    (ht : orderOf t = 2) (htx : t * x * t⁻¹ = x⁻¹) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) ∣
      (Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G) : Subgroup G) :
        Set G)).index - 1 := by
  classical
  set A := Subgroup.centralizer ({x} : Set G)
  set N := Subgroup.normalizer (A : Set G)
  set o : G ⧸ N := QuotientGroup.mk 1
  set F : Set (G ⧸ N) := {q | q ≠ o}
  have hmk : ∀ g : G, (QuotientGroup.mk g : G ⧸ N) = o ↔ g ∈ N := by
    intro g
    rw [QuotientGroup.eq, mul_one, inv_mem_iff]
  have hsmul : ∀ (a g : G), a • (QuotientGroup.mk g : G ⧸ N) = QuotientGroup.mk (a * g) :=
    fun a g => MulAction.Quotient.smul_coe N a g
  have hF : ∀ a ∈ A, ∀ q ∈ F, (a : G) • q ∈ F := by
    intro a ha q hq h0
    apply hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hsmul, hmk] at h0
    rw [hmk]
    have : g = a⁻¹ * (a * g) := by group
    rw [this]
    exact N.mul_mem (N.inv_mem (Subgroup.le_normalizer ha)) h0
  let act : MulAction A F :=
    { smul := fun a q => ⟨(a : G) • (q : G ⧸ N), hF a a.2 q q.2⟩
      one_smul := fun q => Subtype.ext (one_smul G (q : G ⧸ N))
      mul_smul := fun a b q => Subtype.ext (mul_smul (a : G) (b : G) (q : G ⧸ N)) }
  have : Finite F := Set.toFinite _ |>.to_subtype
  have hdvd := card_dvd_of_free (K := A) (X := F) (by
    rintro a ⟨q, hq⟩ haq
    have h1 : (a : G) • q = q := congrArg Subtype.val haq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∉ N := fun hg => hq ((hmk g).mpr hg)
    rw [hsmul, QuotientGroup.eq] at h1
    have h2 : g⁻¹ * (a : G)⁻¹ * g ∈ N := by simpa [mul_assoc] using h1
    have := h.eq_one_of_conj_mem_normalizer hx1 hx ht htx hg (A.inv_mem a.2) h2
    exact Subtype.ext (by simpa using this))
  have hFcard : Nat.card F = N.index - 1 := by
    rw [Nat.card_coe_set_eq]
    have : F = Set.univ \ {o} := by
      ext q
      simp [F]
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]
    rfl
  rw [← hFcard]
  exact hdvd

end JankoHyp

end CFSG.Walter.J1
