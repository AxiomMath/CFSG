module

public import CFSG.GH74.M12.Statements

public section

namespace CFSG.Quasithin

open Subgroup

structure ExtraspecialAt {G : Type*} [Group G] (Q : Subgroup G) (z : G) : Prop where
  card_eq : Nat.card Q = 32
  mem : z ∈ Q
  ne_one : z ≠ 1
  sq_eq : z * z = 1
  central : ∀ q ∈ Q, q * z = z * q
  center_le : ∀ q ∈ Q, (∀ y ∈ Q, q * y = y * q) → q = 1 ∨ q = z
  sq_mem : ∀ q ∈ Q, q * q = 1 ∨ q * q = z
  comm_mem : ∀ q ∈ Q, ∀ y ∈ Q, q * y * q⁻¹ * y⁻¹ = 1 ∨ q * y * q⁻¹ * y⁻¹ = z

section

variable {G : Type*} [Group G]

theorem card_le_two_mul_card_centralizer [Finite G] {z : G} (hz : z * z = 1) {A : Subgroup G}
    (q : G) (hcomm : ∀ a ∈ A, a * q * a⁻¹ * q⁻¹ = 1 ∨ a * q * a⁻¹ * q⁻¹ = z)
    (hcentral : ∀ a ∈ A, a * z = z * a) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer ({q} : Set G)) := by
  classical
  by_cases hA : A ≤ Subgroup.centralizer ({q} : Set G)
  · rw [inf_eq_left.2 hA]; omega
  · obtain ⟨a₀, ha₀, ha₀C⟩ := IsConcreteLE.not_le_iff_exists.1 hA
    have hmem : ∀ a ∈ A, a ∈ Subgroup.centralizer ({q} : Set G) ↔ a * q = q * a := by
      intro a _
      exact Subgroup.mem_centralizer_singleton_iff
    have hz0 : ∀ a ∈ A, a * q ≠ q * a → a * q = z * (q * a) := by
      intro a ha hne
      rcases hcomm a ha with h | h
      · exact absurd (by
          calc a * q = (a * q * a⁻¹ * q⁻¹) * (q * a) := by group
            _ = q * a := by rw [h, one_mul]) hne
      · calc a * q = (a * q * a⁻¹ * q⁻¹) * (q * a) := by group
          _ = z * (q * a) := by rw [h]
    have hsub : (A : Set G) ⊆ ↑(A ⊓ Subgroup.centralizer ({q} : Set G)) ∪
        (fun c => a₀ * c) '' ↑(A ⊓ Subgroup.centralizer ({q} : Set G)) := by
      intro a ha
      by_cases haC : a ∈ Subgroup.centralizer ({q} : Set G)
      · exact Or.inl ⟨ha, haC⟩
      · refine Or.inr ⟨a₀⁻¹ * a, ⟨A.mul_mem (A.inv_mem ha₀) ha, ?_⟩, by group⟩
        show a₀⁻¹ * a ∈ Subgroup.centralizer ({q} : Set G)
        rw [hmem _ (A.mul_mem (A.inv_mem ha₀) ha)]
        have hne : a * q ≠ q * a := fun h => haC ((hmem a ha).2 h)
        have hne₀ : a₀ * q ≠ q * a₀ := fun h => ha₀C ((hmem a₀ ha₀).2 h)
        have h1 := hz0 a ha hne
        have h2 := hz0 a₀ ha₀ hne₀
        have hza : a₀⁻¹ * z = z * a₀⁻¹ := hcentral _ (A.inv_mem ha₀)
        have hq0 : a₀⁻¹ * q = z * (q * a₀⁻¹) := by
          calc a₀⁻¹ * q = a₀⁻¹ * (q * a₀) * a₀⁻¹ := by group
            _ = a₀⁻¹ * (z * (a₀ * q)) * a₀⁻¹ := by
              rw [show q * a₀ = z * (a₀ * q) from by
                calc q * a₀ = z * (z * (q * a₀)) := by rw [← mul_assoc, hz, one_mul]
                  _ = z * (a₀ * q) := by rw [h2]]
            _ = z * (q * a₀⁻¹) := by
              calc a₀⁻¹ * (z * (a₀ * q)) * a₀⁻¹ = (a₀⁻¹ * z) * (a₀ * q) * a₀⁻¹ := by group
                _ = (z * a₀⁻¹) * (a₀ * q) * a₀⁻¹ := by rw [hza]
                _ = z * q * a₀⁻¹ := by group
                _ = z * (q * a₀⁻¹) := by group
        calc a₀⁻¹ * a * q = a₀⁻¹ * (a * q) := by group
          _ = a₀⁻¹ * (z * (q * a)) := by rw [h1]
          _ = (a₀⁻¹ * z) * (q * a) := by group
          _ = (z * a₀⁻¹) * (q * a) := by rw [hza]
          _ = z * ((a₀⁻¹ * q) * a) := by group
          _ = z * ((z * (q * a₀⁻¹)) * a) := by rw [hq0]
          _ = (z * z) * (q * (a₀⁻¹ * a)) := by group
          _ = q * (a₀⁻¹ * a) := by rw [hz, one_mul]
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le (↑(A ⊓ Subgroup.centralizer ({q} : Set G)) : Set G)
      ((fun c => a₀ * c) '' ↑(A ⊓ Subgroup.centralizer ({q} : Set G)))
    rw [Set.ncard_image_of_injective _ (mul_right_injective a₀)] at h2
    have e1 : Nat.card ↥A = (A : Set G).ncard := Nat.card_coe_set_eq _
    have e2 : Nat.card ↥(A ⊓ Subgroup.centralizer ({q} : Set G)) =
        (↑(A ⊓ Subgroup.centralizer ({q} : Set G)) : Set G).ncard := Nat.card_coe_set_eq _
    omega

theorem card_le_two_of_forall {z : G} {C : Subgroup G} (hC : ∀ c ∈ C, c = 1 ∨ c = z) :
    Nat.card C ≤ 2 := by
  have hsub : (C : Set G) ⊆ {1, z} := fun c hc => by
    rcases hC c hc with h | h <;> simp [h]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, z} : Set G).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : G) ({z} : Set G)
    rw [Set.ncard_singleton] at this
    exact this
  have e : Nat.card C = (C : Set G).ncard := Nat.card_coe_set_eq _
  omega

namespace ExtraspecialAt

variable {Q : Subgroup G} {z : G}

theorem card_abelian_le [Finite G] (h : ExtraspecialAt Q z) {A : Subgroup G} (hA : A ≤ Q)
    (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Nat.card A ≤ 8 := by
  by_contra hcon
  push Not at hcon
  have hdvd : Nat.card A ∣ 32 := h.card_eq ▸ Subgroup.card_dvd_of_le hA
  have hd : Nat.divisors 32 = {1, 2, 4, 8, 16, 32} := by decide
  have h16 : Nat.card A = 16 ∨ Nat.card A = 32 := by
    have : Nat.card A ∈ Nat.divisors 32 := by simp [hdvd]
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  rcases h16 with h16 | h32
  · have hne : A ≠ Q := by
      intro e; rw [e, h.card_eq] at h16; omega
    obtain ⟨q, hqQ, hqA⟩ := IsConcreteLE.not_le_iff_exists.1 (show ¬ Q ≤ A from fun hh =>
      hne (le_antisymm hA hh))
    set B : Subgroup G := A ⊔ Subgroup.zpowers q with hB
    have hBQ : B ≤ Q := sup_le hA ((Subgroup.zpowers_le).2 hqQ)
    have hBA : A < B := by
      refine lt_of_le_of_ne le_sup_left (fun e => hqA ?_)
      have : q ∈ B := Subgroup.mem_sup_right (Subgroup.mem_zpowers q)
      rw [← e] at this; exact this
    have hdvdB : Nat.card B ∣ 32 := h.card_eq ▸ Subgroup.card_dvd_of_le hBQ
    have hAB : Nat.card A < Nat.card B := Subgroup.card_lt_of_lt hBA
    have hB32 : Nat.card B = 32 := by
      have : Nat.card B ∈ Nat.divisors 32 := by simp [hdvdB]
      rw [hd] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    have hBeq : B = Q := Subgroup.eq_of_le_of_card_ge hBQ (by rw [hB32, h.card_eq])
    have hcent : ∀ c ∈ A ⊓ Subgroup.centralizer ({q} : Set G), c = 1 ∨ c = z := by
      intro c hc
      apply h.center_le c (hA hc.1)
      intro y hy
      have hy' : y ∈ B := hBeq ▸ hy
      have hle : B ≤ Subgroup.centralizer ({c} : Set G) := by
        refine sup_le ?_ ?_
        · intro a ha
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hab a ha c hc.1
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.1 hc.2).symm
      have := Subgroup.mem_centralizer_singleton_iff.1 (hle hy')
      exact this.symm
    have hC2 := card_le_two_of_forall hcent
    have hcount := card_le_two_mul_card_centralizer h.sq_eq (A := A) q
      (fun a ha => h.comm_mem a (hA ha) q hqQ) (fun a ha => h.central a (hA ha))
    omega
  · have hAQ : A = Q := Subgroup.eq_of_le_of_card_ge hA (by rw [h32, h.card_eq])
    subst hAQ
    have := card_le_two_of_forall (z := z) (C := A) (fun q hq => h.center_le q hq (fun y hy => hab q hq y hy))
    omega

theorem exists_sq_eq_of_noncentral [Finite G] (h : ExtraspecialAt Q z) {s : G} (hs : s ∈ Q)
    (hs1 : s ≠ 1) (hsz : s ≠ z) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({s} : Set G)) = 16 ∧
      ∃ x ∈ Q ⊓ Subgroup.centralizer ({s} : Set G), x * x = z := by
  set C := Q ⊓ Subgroup.centralizer ({s} : Set G) with hC
  have hcount : 32 ≤ 2 * Nat.card C := by
    have := card_le_two_mul_card_centralizer h.sq_eq (A := Q) s
      (fun a ha => h.comm_mem a ha s hs) (fun a ha => h.central a ha)
    rw [h.card_eq] at this
    exact this
  have hCQ : C ≤ Q := inf_le_left
  have hdvd : Nat.card C ∣ 32 := h.card_eq ▸ Subgroup.card_dvd_of_le hCQ
  have hne : C ≠ Q := by
    intro e
    have : Q ≤ Subgroup.centralizer ({s} : Set G) := by
      rw [← e]; exact inf_le_right
    rcases h.center_le s hs (fun y hy => (Subgroup.mem_centralizer_singleton_iff.1 (this hy)).symm)
      with h1 | h1
    · exact hs1 h1
    · exact hsz h1
  have hlt : Nat.card C < 32 := by
    have := Subgroup.card_lt_of_lt (lt_of_le_of_ne hCQ hne)
    rwa [h.card_eq] at this
  have hd : Nat.divisors 32 = {1, 2, 4, 8, 16, 32} := by decide
  have h16 : Nat.card C = 16 := by
    have : Nat.card C ∈ Nat.divisors 32 := by simp [hdvd]
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  refine ⟨h16, ?_⟩
  by_contra hno
  push Not at hno
  have hsq : ∀ x ∈ C, x * x = 1 := fun x hx =>
    (h.sq_mem x (hCQ hx)).resolve_right (hno x hx)
  have hab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
    intro a ha b hb
    have h1 := hsq _ (C.mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = b * a := by rw [mul_inv_rev, ha', hb']
  have := h.card_abelian_le hCQ hab
  omega

end ExtraspecialAt

section Conj

variable {Q : Subgroup G} {z : G}

theorem mem_map_conj_iff (Q : Subgroup G) (g x : G) :
    x ∈ Q.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ Q := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hq
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem ExtraspecialAt.conj (h : ExtraspecialAt Q z) (g : G) :
    ExtraspecialAt (Q.map (MulAut.conj g).toMonoidHom) (g * z * g⁻¹) where
  card_eq := by
    rw [← h.card_eq]
    exact Nat.card_congr (Subgroup.equivMapOfInjective Q (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm
  mem := by
    rw [mem_map_conj_iff]
    simpa [mul_assoc] using h.mem
  ne_one := by
    intro e
    apply h.ne_one
    have : g⁻¹ * (g * z * g⁻¹) * g = g⁻¹ * 1 * g := by rw [e]
    simpa [mul_assoc] using this
  sq_eq := by
    have := congrArg (fun y => g * y * g⁻¹) h.sq_eq
    simpa [mul_assoc] using this
  central := by
    intro q hq
    rw [mem_map_conj_iff] at hq
    have := h.central _ hq
    have h2 := congrArg (fun y => g * y * g⁻¹) this
    simpa [mul_assoc] using h2
  center_le := by
    intro q hq hc
    rw [mem_map_conj_iff] at hq
    have := h.center_le _ hq (fun y hy => by
      have hy' : g * y * g⁻¹ ∈ Q.map (MulAut.conj g).toMonoidHom := by
        rw [mem_map_conj_iff]; simpa [mul_assoc] using hy
      have := hc _ hy'
      have h2 := congrArg (fun w => g⁻¹ * w * g) this
      simpa [mul_assoc] using h2)
    rcases this with h1 | h1
    · left
      have := congrArg (fun w => g * w * g⁻¹) h1
      simpa [mul_assoc] using this
    · right
      have := congrArg (fun w => g * w * g⁻¹) h1
      simpa [mul_assoc] using this
  sq_mem := by
    intro q hq
    rw [mem_map_conj_iff] at hq
    rcases h.sq_mem _ hq with h1 | h1
    · left
      have := congrArg (fun w => g * w * g⁻¹) h1
      simpa [mul_assoc] using this
    · right
      have := congrArg (fun w => g * w * g⁻¹) h1
      simpa [mul_assoc] using this
  comm_mem := by
    intro q hq y hy
    rw [mem_map_conj_iff] at hq hy
    rcases h.comm_mem _ hq _ hy with h1 | h1
    · left
      have := congrArg (fun w => g * w * g⁻¹) h1
      simpa [mul_assoc] using this
    · right
      have := congrArg (fun w => g * w * g⁻¹) h1
      simpa [mul_assoc] using this

end Conj

variable {z : G}

abbrev ascH (z : G) : Subgroup G := Subgroup.centralizer ({z} : Set G)

@[expose] def ascQ (z : G) : Subgroup G := (CFSG.pCore 2 ↥(ascH z)).map (ascH z).subtype

theorem ascQ_le_ascH (z : G) : ascQ z ≤ ascH z := Subgroup.map_subtype_le _

theorem mem_ascQ_iff (z q : G) :
    q ∈ ascQ z ↔ ∃ h : q ∈ ascH z, (⟨q, h⟩ : ↥(ascH z)) ∈ CFSG.pCore 2 ↥(ascH z) := by
  unfold ascQ
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hq⟩
    exact ⟨⟨q, h⟩, hq, rfl⟩

theorem isExtraspecial_facts {K : Type*} [Group K] (hK : CFSG.IsExtraspecial 2 K) :
    Nat.card (Subgroup.center K) = 2 ∧ (∀ x : K, x ^ 2 ∈ Subgroup.center K) ∧
      (∀ x y : K, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center K) := by
  refine ⟨CFSG.IsExtraspecial.center_order_p 2 K, ?_, ?_⟩
  · intro x
    have hE := CFSG.IsExtraspecial.quotient_elementary_abelian 2 K
    have h2 : ∀ y : K ⧸ Subgroup.center K, y ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (CFSG.IsElementaryAbelian.exponent_dvd_p 2 (K ⧸ Subgroup.center K))
    have := h2 (x : K ⧸ Subgroup.center K)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at this
    exact this
  · intro x y
    have hE := CFSG.IsExtraspecial.quotient_elementary_abelian 2 K
    have : ((x * y * x⁻¹ * y⁻¹ : K) : K ⧸ Subgroup.center K) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hE.toIsMulCommutative.is_comm.comm (x : K ⧸ Subgroup.center K) (y : K ⧸ Subgroup.center K)]
      group
    exact (QuotientGroup.eq_one_iff _).1 this

theorem eq_one_or_eq_of_card_two {K : Type*} [Group K] (hK : Nat.card K = 2) {a : K} (ha : a ≠ 1)
    (x : K) : x = 1 ∨ x = a := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  by_contra hcon
  push Not at hcon
  have h3 : ({1, a, x} : Set K).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm hcon.2)]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm ha, Ne.symm hcon.1⟩
  have h4 := Set.ncard_le_ncard (Set.subset_univ ({1, a, x} : Set K)) (Set.toFinite _)
  rw [Set.ncard_univ] at h4
  omega

theorem z_mem_ascH (z : G) : z ∈ ascH z := Subgroup.mem_centralizer_singleton_iff.2 rfl

theorem z_mem_pCore (hyp : CFSG.GH74.M12.Asc03Hyp G z) :
    (⟨z, z_mem_ascH z⟩ : ↥(ascH z)) ∈ CFSG.pCore 2 ↥(ascH z) := by
  set zH : ↥(ascH z) := ⟨z, z_mem_ascH z⟩ with hzH
  have hord : orderOf zH = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hyp.orderTwo
  have hnormal : (Subgroup.zpowers zH).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g zH := by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 g.2
    rw [(hc.zpow_right k).eq]
    simp
  have hp : IsPGroup 2 (Subgroup.zpowers zH) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]; norm_num
  have hle : Subgroup.zpowers zH ≤ CFSG.pCore 2 ↥(ascH z) := le_sSup ⟨hnormal, hp⟩
  exact hle (Subgroup.mem_zpowers zH)

theorem extraspecialAt_ascQ (hyp : CFSG.GH74.M12.Asc03Hyp G z) : ExtraspecialAt (ascQ z) z := by
  obtain ⟨hcard, hsq, hcomm⟩ := isExtraspecial_facts hyp.extraspecial
  set P := CFSG.pCore 2 ↥(ascH z) with hP
  set zH : ↥(ascH z) := ⟨z, z_mem_ascH z⟩ with hzH
  have hzP : zH ∈ P := z_mem_pCore hyp
  have hz1 : z ≠ 1 := fun h => by
    have := hyp.orderTwo
    rw [h, orderOf_one] at this
    omega
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hyp.orderTwo, pow_two] at this
    exact this
  let zP : ↥P := ⟨zH, hzP⟩
  have hzPc : zP ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 y.1.2
  have hzP1 : zP ≠ 1 := fun h => hz1 (by
    have := congrArg (fun w : ↥P => ((w : ↥(ascH z)) : G)) h
    simpa [zP, zH] using this)
  have hcen : ∀ w ∈ Subgroup.center ↥P, w = 1 ∨ w = zP := by
    intro w hw
    have := eq_one_or_eq_of_card_two hcard (a := (⟨zP, hzPc⟩ : ↥(Subgroup.center ↥P)))
      (by intro h; exact hzP1 (congrArg Subtype.val h)) ⟨w, hw⟩
    rcases this with h | h
    · left; exact congrArg Subtype.val h
    · right; exact congrArg Subtype.val h
  have hmemQ : ∀ w : ↥P, ((w : ↥(ascH z)) : G) ∈ ascQ z := fun w =>
    (mem_ascQ_iff z _).2 ⟨w.1.2, w.2⟩
  refine ⟨?_, ?_, hz1, hz2, ?_, ?_, ?_, ?_⟩
  · exact ((Nat.card_congr (Subgroup.equivMapOfInjective P (ascH z).subtype
      (ascH z).subtype_injective).toEquiv).symm).trans hyp.card_core
  · rw [mem_ascQ_iff]; exact ⟨z_mem_ascH z, hzP⟩
  · intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.1 (ascQ_le_ascH z hq)
  · intro q hq hc
    obtain ⟨hqH, hqP⟩ := (mem_ascQ_iff z q).1 hq
    have hqc : (⟨⟨q, hqH⟩, hqP⟩ : ↥P) ∈ Subgroup.center ↥P := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      apply Subtype.ext
      exact (hc _ (hmemQ y)).symm
    rcases hcen _ hqc with h | h
    · left; simpa using congrArg (fun w : ↥P => ((w : ↥(ascH z)) : G)) h
    · right; simpa [zP, zH] using congrArg (fun w : ↥P => ((w : ↥(ascH z)) : G)) h
  · intro q hq
    obtain ⟨hqH, hqP⟩ := (mem_ascQ_iff z q).1 hq
    have h1 := hcen _ (hsq (⟨⟨q, hqH⟩, hqP⟩ : ↥P))
    rcases h1 with h | h
    · left; simpa [pow_two] using congrArg (fun w : ↥P => ((w : ↥(ascH z)) : G)) h
    · right; simpa [pow_two, zP, zH] using congrArg (fun w : ↥P => ((w : ↥(ascH z)) : G)) h
  · intro q hq y hy
    obtain ⟨hqH, hqP⟩ := (mem_ascQ_iff z q).1 hq
    obtain ⟨hyH, hyP⟩ := (mem_ascQ_iff z y).1 hy
    have h1 := hcen _ (hcomm (⟨⟨q, hqH⟩, hqP⟩ : ↥P) (⟨⟨y, hyH⟩, hyP⟩ : ↥P))
    rcases h1 with h | h
    · left; simpa using congrArg (fun w : ↥P => ((w : ↥(ascH z)) : G)) h
    · right; simpa [zP, zH] using congrArg (fun w : ↥P => ((w : ↥(ascH z)) : G)) h

theorem sq_mem_ascQ_of_pow_four (hyp : CFSG.GH74.M12.Asc03Hyp G z) {h : G} (hH : h ∈ ascH z)
    (h4 : h ^ 4 = 1) : h * h ∈ ascQ z := by
  obtain ⟨e⟩ := hyp.quotient_S3
  have hperm : ∀ y : Equiv.Perm (Fin 3), y ^ 4 = 1 → y ^ 2 = 1 := by decide
  set P := CFSG.pCore 2 ↥(ascH z) with hP
  have h1 : (e (QuotientGroup.mk (⟨h, hH⟩ : ↥(ascH z)) : ↥(ascH z) ⧸ P)) ^ 4 = 1 := by
    rw [← map_pow, ← QuotientGroup.mk_pow]
    have : (⟨h, hH⟩ : ↥(ascH z)) ^ 4 = 1 := Subtype.ext (by simpa using h4)
    rw [this, QuotientGroup.mk_one, map_one]
  have h2 := hperm _ h1
  rw [← map_pow, ← QuotientGroup.mk_pow] at h2
  have h3 : ((⟨h, hH⟩ : ↥(ascH z)) ^ 2) ∈ P := by
    have := e.injective (h2.trans (map_one e).symm)
    exact (QuotientGroup.eq_one_iff _).1 this
  rw [mem_ascQ_iff]
  refine ⟨(ascH z).mul_mem hH hH, ?_⟩
  have : (⟨h * h, (ascH z).mul_mem hH hH⟩ : ↥(ascH z)) = (⟨h, hH⟩ : ↥(ascH z)) ^ 2 :=
    Subtype.ext (by simp [pow_two])
  rw [this]; exact h3

theorem card_le_two_mul_card_inf_ascQ [Finite G] (hyp : CFSG.GH74.M12.Asc03Hyp G z)
    {C : Subgroup G} (hCH : C ≤ ascH z) (hC : IsPGroup 2 C) :
    Nat.card C ≤ 2 * Nat.card ↥(C ⊓ ascQ z) := by
  obtain ⟨e⟩ := hyp.quotient_S3
  set P := CFSG.pCore 2 ↥(ascH z) with hP
  let ψ : ↥C →* Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' P).comp (Subgroup.inclusion hCH))
  have hker : ∀ c : ↥C, c ∈ ψ.ker ↔ ((c : G)) ∈ ascQ z := by
    intro c
    rw [MonoidHom.mem_ker, mem_ascQ_iff]
    constructor
    · intro hc
      refine ⟨hCH c.2, ?_⟩
      have : (QuotientGroup.mk' P) (Subgroup.inclusion hCH c) = 1 := by
        apply e.injective
        simpa [ψ] using hc
      exact (QuotientGroup.eq_one_iff _).1 this
    · rintro ⟨hcH, hcP⟩
      have : (QuotientGroup.mk' P) (Subgroup.inclusion hCH c) = 1 :=
        (QuotientGroup.eq_one_iff _).2 hcP
      show e ((QuotientGroup.mk' P) (Subgroup.inclusion hCH c)) = 1
      rw [this, map_one]
  have hkerCard : Nat.card ψ.ker = Nat.card ↥(C ⊓ ascQ z) :=
    Nat.card_congr
      { toFun := fun c => ⟨(c.1 : G), c.1.2, (hker c.1).1 c.2⟩
        invFun := fun c => ⟨⟨c.1, c.2.1⟩, (hker _).2 c.2.2⟩
        left_inv := fun c => rfl
        right_inv := fun c => rfl }
  have h1 : Nat.card ψ.ker * Nat.card ψ.range = Nat.card C := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hrange2 : Nat.card ψ.range ≤ 2 := by
    have hp : IsPGroup 2 ψ.range :=
      hC.of_surjective ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ)
    have hdvd : Nat.card ψ.range ∣ Nat.card (Equiv.Perm (Fin 3)) :=
      Subgroup.card_subgroup_dvd_card _
    have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
    rw [h6, hn] at hdvd
    rw [hn]
    by_contra hcon
    have hn2 : 2 ≤ n := by
      by_contra hlt
      push Not at hlt
      interval_cases n <;> simp at hcon
    have := (Nat.pow_dvd_pow 2 hn2).trans hdvd
    omega
  rw [← h1, hkerCard]
  have := Nat.card_pos (α := ψ.ker)
  nlinarith

theorem config_of_conj [Finite G] (hyp : CFSG.GH74.M12.Asc03Hyp G z) {g : G}
    (hgz : g * z * g⁻¹ ≠ z) (hsQ : g * z * g⁻¹ ∈ ascQ z) :
    g⁻¹ * z * g ∈ ascQ z ∧
      Nat.card ↥(ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom) = 8 ∧
      (∀ x ∈ ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom, x * x = 1 ∧
        ∀ y ∈ ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom, x * y = y * x) ∧
      Nat.card ↥(ascH z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom) = 16 ∧
      ∃ v₀ ∈ ascH z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom, orderOf v₀ = 2 ∧
        v₀ ∉ ascQ z := by
  have hE := extraspecialAt_ascQ hyp
  have hEg : ExtraspecialAt ((ascQ z).map (MulAut.conj g).toMonoidHom) (g * z * g⁻¹) := hE.conj g
  have hs1 : g * z * g⁻¹ ≠ 1 := hEg.ne_one
  obtain ⟨-, x₀, hx₀, hx₀sq⟩ := hE.exists_sq_eq_of_noncentral hsQ hs1 hgz
  have hx₀s : x₀ * (g * z * g⁻¹) = (g * z * g⁻¹) * x₀ :=
    Subgroup.mem_centralizer_singleton_iff.1 hx₀.2
  have hhH : g⁻¹ * x₀ * g ∈ ascH z := by
    rw [ascH, Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * x₀ * g * z = g⁻¹ * (x₀ * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x₀) * g := by rw [hx₀s]
      _ = z * (g⁻¹ * x₀ * g) := by group
  have hhh : (g⁻¹ * x₀ * g) * (g⁻¹ * x₀ * g) = g⁻¹ * z * g := by
    calc (g⁻¹ * x₀ * g) * (g⁻¹ * x₀ * g) = g⁻¹ * (x₀ * x₀) * g := by group
      _ = g⁻¹ * z * g := by rw [hx₀sq]
  have hzQ : g⁻¹ * z * g ∈ ascQ z := by
    rw [← hhh]
    refine sq_mem_ascQ_of_pow_four hyp hhH ?_
    calc (g⁻¹ * x₀ * g) ^ 4 = ((g⁻¹ * x₀ * g) * (g⁻¹ * x₀ * g)) * ((g⁻¹ * x₀ * g) * (g⁻¹ * x₀ * g)) := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := by rw [hhh]; calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
                                    _ = 1 := by rw [hE.sq_eq]; group
  have hzQg : z ∈ (ascQ z).map (MulAut.conj g).toMonoidHom := (mem_map_conj_iff _ g z).2 hzQ
  have hC16 : Nat.card ↥(ascH z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom) = 16 := by
    have := (hEg.exists_sq_eq_of_noncentral hzQg hE.ne_one (Ne.symm hgz)).1
    rw [inf_comm]
    exact this
  have helem : ∀ x ∈ ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom, x * x = 1 ∧
      ∀ y ∈ ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom, x * y = y * x := by
    intro x hx
    refine ⟨?_, fun y hy => ?_⟩
    · rcases hE.sq_mem x hx.1 with h1 | h1
      · exact h1
      · rcases hEg.sq_mem x hx.2 with h2 | h2
        · exact h2
        · exact absurd (h1.symm.trans h2) (Ne.symm hgz)
    · have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by
        rcases hE.comm_mem x hx.1 y hy.1 with h1 | h1
        · exact h1
        · rcases hEg.comm_mem x hx.2 y hy.2 with h2 | h2
          · exact h2
          · exact absurd (h1.symm.trans h2) (Ne.symm hgz)
      calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = y * x := by rw [h1, one_mul]
  have hE8le : Nat.card ↥(ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom) ≤ 8 :=
    hE.card_abelian_le inf_le_left (fun a ha b hb => (helem a ha).2 b hb)
  have hQgp : IsPGroup 2 ↥((ascQ z).map (MulAut.conj g).toMonoidHom) :=
    IsPGroup.of_card (n := 5) (by rw [hEg.card_eq]; norm_num)
  have hCp : IsPGroup 2 ↥(ascH z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom) :=
    hQgp.to_le inf_le_right
  have hEeq : (ascH z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom) ⊓ ascQ z =
      ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩; exact ⟨⟨ascQ_le_ascH z h3, h2⟩, h3⟩
  have hE8ge : 8 ≤ Nat.card ↥(ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom) := by
    have := card_le_two_mul_card_inf_ascQ hyp (inf_le_left : ascH z ⊓ (ascQ z).map
      (MulAut.conj g).toMonoidHom ≤ ascH z) hCp
    rw [hEeq, hC16] at this
    omega
  have hE8 : Nat.card ↥(ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom) = 8 :=
    le_antisymm hE8le hE8ge
  have hinv : ∃ v ∈ ascH z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom, v * v = 1 ∧
      v ∉ ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom := by
    by_contra hno
    push Not at hno
    have hEC : ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom ≤
        ascH z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom :=
      le_inf (le_trans inf_le_left (ascQ_le_ascH z)) inf_le_right
    have hnle : ¬ ascH z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom ≤
        ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom := by
      intro hle
      have := Subgroup.card_le_of_le hle
      omega
    obtain ⟨c, hcC, hcE⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
    have hsq : ∀ y ∈ ascH z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom,
        y ∉ ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom → y * y = g * z * g⁻¹ := by
      intro y hyC hyE
      rcases hEg.sq_mem y hyC.2 with h1 | h1
      · exact absurd (hno y hyC h1) hyE
      · exact h1
    have hcomm : ∀ e ∈ ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom, c * e = e * c := by
      intro e he
      have hceE : c * e ∉ ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom := by
        intro h
        apply hcE
        have := Subgroup.mul_mem _ h (Subgroup.inv_mem _ he)
        simpa using this
      have h1 := hsq (c * e) (Subgroup.mul_mem _ hcC (hEC he)) hceE
      have h2 := hsq c hcC hcE
      have he2 : e * e = 1 := (helem e he).1
      have h3 : e * c * e = c := by
        have : c * (e * c * e) = c * c := by
          calc c * (e * c * e) = (c * e) * (c * e) := by group
            _ = g * z * g⁻¹ := h1
            _ = c * c := h2.symm
        exact mul_left_cancel this
      calc c * e = (e * c * e) * e := by rw [h3]
        _ = e * c * (e * e) := by group
        _ = e * c := by rw [he2, mul_one]
    have hSc : ∀ a ∈ ((ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ∪ {c},
        ∀ b ∈ ((ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ∪ {c},
        a * b = b * a := by
      rintro a (ha | ha) b (hb | hb)
      · exact (helem a ha).2 b hb
      · rw [Set.mem_singleton_iff.1 hb]; exact (hcomm a ha).symm
      · rw [Set.mem_singleton_iff.1 ha]; exact hcomm b hb
      · rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]
    let B : Subgroup G := Subgroup.closure
      (((ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ∪ {c})
    have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
      have := Subgroup.isMulCommutative_closure
        (k := ((ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ∪ {c})
        (fun x hx y hy _ => hSc x hx y hy)
      intro a ha b hb
      exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : B) ⟨b, hb⟩)
    have hBQg : B ≤ (ascQ z).map (MulAut.conj g).toMonoidHom := by
      refine (Subgroup.closure_le _).2 (Set.union_subset (fun x hx => hx.2) ?_)
      rintro y rfl
      exact hcC.2
    have hEB : ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom ≤ B := fun x hx =>
      Subgroup.subset_closure (Or.inl hx)
    have hcB : c ∈ B := Subgroup.subset_closure (Or.inr rfl)
    have hlt : ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom < B :=
      lt_of_le_of_ne hEB (fun e => hcE (e ▸ hcB))
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 := hEg.card_abelian_le hBQg hBab
    omega
  obtain ⟨v₀, hv₀C, hv₀sq, hv₀E⟩ := hinv
  have hv₀1 : v₀ ≠ 1 := fun h => hv₀E (h ▸ Subgroup.one_mem _)
  refine ⟨hzQ, hE8, helem, hC16, v₀, hv₀C,
    orderOf_eq_prime (by rwa [pow_two]) hv₀1, fun hQ => hv₀E ⟨hQ, hv₀C.2⟩⟩

theorem exists_config_of_asc03 [Finite G] (hyp : CFSG.GH74.M12.Asc03Hyp G z) :
    ∃ g : G, g * z * g⁻¹ ≠ z ∧ g * z * g⁻¹ ∈ ascQ z ∧ g⁻¹ * z * g ∈ ascQ z ∧
      Nat.card ↥(ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom) = 8 ∧
      (∀ x ∈ ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom, x * x = 1 ∧
        ∀ y ∈ ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom, x * y = y * x) ∧
      Nat.card ↥(ascH z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom) = 16 ∧
      ∃ v₀ ∈ ascH z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom, orderOf v₀ = 2 ∧
        v₀ ∉ ascQ z := by
  obtain ⟨g, hgz, q, hqP, hq⟩ := hyp.not_weakly_closed
  have hsQ : g * z * g⁻¹ ∈ ascQ z := by
    rw [← hq]
    exact (mem_ascQ_iff z _).2 ⟨q.2, hqP⟩
  exact ⟨g, hgz, hsQ, config_of_conj hyp hgz hsQ⟩

end

end CFSG.Quasithin
