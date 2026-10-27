module

public import CFSG.Quasithin.Background.D2Z8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem conj_mem_zpowers_of_inv {G : Type*} [Group G] {a u : G} (hinv : u * a * u⁻¹ = a⁻¹) :
    ∀ x ∈ Subgroup.zpowers a, u * x * u⁻¹ ∈ Subgroup.zpowers a := by
  intro x hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow, hinv, inv_zpow]
  exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) j)

omit [Finite V] in
theorem mem_sup_zpowers_of_inv {G : Type*} [Group G] {a u : G} (hu2 : u ^ 2 = 1)
    (hinv : u * a * u⁻¹ = a⁻¹) {x : G} (hx : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers u) :
    ∃ y ∈ Subgroup.zpowers a, ∃ z ∈ Subgroup.zpowers u, x = y * z := by
  have hn : Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => conj_mem_zpowers_of_inv hinv h hh
    · intro hh
      have := conj_mem_zpowers_of_inv hinv _ hh
      have e : u * (u * h * u⁻¹) * u⁻¹ = h := by
        calc u * (u * h * u⁻¹) * u⁻¹ = (u * u) * h * (u * u)⁻¹ := by group
          _ = h := by rw [← pow_two, hu2]; simp
      rwa [e] at this
  have hx' := hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at hx'
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp hx'
  exact ⟨y, hy, z, hz, rfl⟩

omit [Finite V] in
theorem mem_zpowers_of_commute {G : Type*} [Group G] {a u : G} (hao : orderOf a = 3)
    (hu2 : u ^ 2 = 1) (hinv : u * a * u⁻¹ = a⁻¹)
    {x : G} (hx : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers u) (hxa : a * x = x * a) :
    x ∈ Subgroup.zpowers a := by
  obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup_zpowers_of_inv hu2 hinv hx
  have hya : a * y = y * a := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.refl a).zpow_right j).eq
  have hza : a * z = z * a := by
    have h1 : a * (y * z) = (y * z) * a := hxa
    calc a * z = y⁻¹ * (y * a) * z := by group
      _ = y⁻¹ * (a * y) * z := by rw [hya]
      _ = y⁻¹ * (a * (y * z)) := by group
      _ = y⁻¹ * ((y * z) * a) := by rw [h1]
      _ = z * a := by group
  have hz' : z = 1 := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rcases zpow_involution hu2 j with h | h
    · exact h
    · exfalso
      rw [h] at hza
      have : u * a * u⁻¹ = a := by rw [← hza, mul_inv_cancel_right]
      rw [hinv] at this
      have h2 : a ^ 2 = 1 := by
        have : a * a = 1 := mul_eq_one_iff_eq_inv.mpr this.symm
        rwa [← pow_two] at this
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hao] at this
      omega
  rw [hz', mul_one]
  exact hy

omit [Finite V] in
theorem sup_zpowers_commute {G : Type*} [Group G] {a u b t : G} (hab : a * b = b * a)
    (hat : a * t = t * a) (hub : u * b = b * u) (hut : u * t = t * u) :
    ∀ x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers u, ∀ y ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers t,
      x * y = y * x := by
  have h2 : ∀ g : G, (b * g = g * b) → (t * g = g * t) →
      Subgroup.zpowers b ⊔ Subgroup.zpowers t ≤ Subgroup.centralizer ({g} : Set G) := by
    intro g hb ht
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hb
    · exact Subgroup.mem_centralizer_singleton_iff.mpr ht
  have hL : Subgroup.zpowers a ⊔ Subgroup.zpowers u ≤
      Subgroup.centralizer ((Subgroup.zpowers b ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (h2 a hab.symm hat.symm hy)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (h2 u hub.symm hut.symm hy)
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (hL hx) y hy).symm

section Two

variable {X A : Subgroup (MulAut V)} {r : ℚ}

theorem dihedral_sub (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u a : MulAut V}
    (k : KleinData A t u) (haQ : a ∈ centR X t) (hao : orderOf a = 3) :
    Nonempty (↥(Subgroup.zpowers a ⊔ Subgroup.zpowers u) ≃* DihedralGroup 3) ∧
      (Subgroup.zpowers a ⊔ Subgroup.zpowers u) ⊓ pCoreOf 3 X = Subgroup.zpowers a := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hinv : u * a * u⁻¹ = a⁻¹ := inverts_centR hV h k a haQ
  have huo : orderOf u = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime k.hb2 k.hb1
  have haP : a ∈ pCoreOf 3 X := centR_le_pCoreOf X t haQ
  refine ⟨nonempty_mulEquiv_dihedral_of_subgroup (by norm_num)
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
    hao huo hinv (fun g hg => hg), ?_⟩
  apply le_antisymm
  · rintro x ⟨hxL, hxP⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup_zpowers_of_inv k.hb2 hinv hxL
    have hyP : y ∈ pCoreOf 3 X := (Subgroup.zpowers_le.mpr haP) hy
    have hzP : z ∈ pCoreOf 3 X := by
      have := (pCoreOf 3 X).mul_mem ((pCoreOf 3 X).inv_mem hyP) hxP
      simpa using this
    have hz1 : z = 1 := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rcases zpow_involution k.hb2 j with h' | h'
      · exact h'
      · exfalso
        rw [h'] at hzP
        exact k.hb1 (eq_one_of_sq_eq_one_of_mem_pCoreOf hzP k.hb2)
    rw [hz1, mul_one]
    exact hy
  · exact le_inf le_sup_left (Subgroup.zpowers_le.mpr haP)

omit [Finite V] in
theorem ab_orders {a b : MulAut V} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hne : Subgroup.zpowers a ≠ Subgroup.zpowers b) :
    orderOf (a * b) = 3 ∧ orderOf (a * b * b) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcab : Commute a b := hab
  have hc3 : (a * b) ^ 3 = 1 := by rw [hcab.mul_pow, ha3, hb3, one_mul]
  have hc'3 : (a * b * b) ^ 3 = 1 := by
    have h1 : Commute a (b * b) := hcab.mul_right hcab
    calc (a * b * b) ^ 3 = (a * (b * b)) ^ 3 := by rw [mul_assoc]
      _ = a ^ 3 * (b * b) ^ 3 := h1.mul_pow 3
      _ = 1 := by
        rw [(Commute.refl b).mul_pow, ha3, hb3]
        simp
  have hc1 : a * b ≠ 1 := by
    intro hh
    apply hne
    have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right hh
    rw [hb', Subgroup.zpowers_inv]
  have hc'1 : a * b * b ≠ 1 := by
    intro hh
    apply hne
    have e1 : a * (b * b) = 1 := by rwa [← mul_assoc]
    have e2 : a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left e1
    have e3 : (b * b)⁻¹ = b := by
      rw [inv_eq_iff_mul_eq_one]
      calc b * b * b = b ^ 3 := (pow_three' b).symm
        _ = 1 := hb3
    have : a = b := by rw [e2, e3]
    rw [this]
  exact ⟨orderOf_eq_prime hc3 hc1, orderOf_eq_prime hc'3 hc'1⟩

theorem two_dihedral (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u a b : MulAut V}
    (k : KleinData A t u) (haQ : a ∈ centR X t) (hbQ : b ∈ centR X u)
    (haz : Subgroup.zpowers a = centR X t) (hbz : Subgroup.zpowers b = centR X u)
    (hao : orderOf a = 3) (hbo : orderOf b = 3) (h3 : centR X (t * u) = ⊥) :
    ∃ L₁ L₂ : Subgroup (MulAut V), (∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) ∧ L₁ ⊓ L₂ = ⊥ ∧
      L₁ ⊔ L₂ = pCoreOf 3 X ⊔ A ∧ Nonempty (↥L₁ ≃* DihedralGroup 3) ∧
      Nonempty (↥L₂ ≃* DihedralGroup 3) ∧
      (Subgroup.zpowers (a * b) ⊓ L₁ = ⊥ ∧ Subgroup.zpowers (a * b) ⊓ L₂ = ⊥) ∧
      (Subgroup.zpowers (a * b * b) ⊓ L₁ = ⊥ ∧ Subgroup.zpowers (a * b * b) ⊓ L₂ = ⊥) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hD1, hP1⟩ := dihedral_sub hV h k haQ hao
  obtain ⟨hD2, hP2⟩ := dihedral_sub hV h k.symm hbQ hbo
  have haP : a ∈ pCoreOf 3 X := centR_le_pCoreOf X t haQ
  have hbP : b ∈ pCoreOf 3 X := centR_le_pCoreOf X u hbQ
  have hab : a * b = b * a := centR_comm hV h t u a haQ b hbQ
  have hat : a * t = t * a := (mem_centR.mp haQ).2
  have hub : u * b = b * u := (mem_centR.mp hbQ).2.symm
  have hut : u * t = t * u := k.comm.symm
  have hinvA : u * a * u⁻¹ = a⁻¹ := inverts_centR hV h k a haQ
  have hinvB : t * b * t⁻¹ = b⁻¹ := inverts_centR hV h k.symm b hbQ
  have hcomm := sup_zpowers_commute hab hat hub hut
  have ha3 : a ^ 3 = 1 := by rw [← hao]; exact pow_orderOf_eq_one a
  have hb3 : b ^ 3 = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  have hacard : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hao]
  have hbcard : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hbo]
  have ha1 : a ≠ 1 := fun e => by rw [e, orderOf_one] at hao; omega
  have hb1 : b ≠ 1 := fun e => by rw [e, orderOf_one] at hbo; omega
  have hne : Subgroup.zpowers a ≠ Subgroup.zpowers b := by
    intro heq
    have : a ∈ centR X t ⊓ centR X u := ⟨haQ, by rw [← hbz, ← heq]; exact Subgroup.mem_zpowers a⟩
    rw [centR_inf_eq_bot hV h k, Subgroup.mem_bot] at this
    exact ha1 this
  obtain ⟨hoc, hoc'⟩ := ab_orders ha3 hb3 hab hne
  have hcc : Nat.card (Subgroup.zpowers (a * b)) = 3 := by rw [Nat.card_zpowers, hoc]
  have hcc' : Nat.card (Subgroup.zpowers (a * b * b)) = 3 := by rw [Nat.card_zpowers, hoc']
  have hbb_mem : ∀ {g : MulAut V}, g ∈ Subgroup.zpowers a → g * g ∈ Subgroup.zpowers a :=
    fun hg => Subgroup.mul_mem _ hg hg
  have hbb : b * b * (b * b) = b := by
    calc b * b * (b * b) = (b * b * b) * b := by group
      _ = b ^ 3 * b := by rw [pow_three']
      _ = b := by rw [hb3, one_mul]
  have hnA : ∀ g, (g = a * b ∨ g = a * b * b) → g ∈ Subgroup.zpowers a → False := by
    intro g hg hga
    apply hne
    have hbmem : b ∈ Subgroup.zpowers a := by
      rcases hg with rfl | rfl
      · have h1 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) hga
        have e : a⁻¹ * (a * b) = b := by group
        rwa [e] at h1
      · have h1 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) hga
        have e : a⁻¹ * (a * b * b) = b * b := by group
        rw [e] at h1
        have h2 := Subgroup.mul_mem _ h1 h1
        rwa [hbb] at h2
    exact (zpowers_eq_of_prime_card hacard hbmem hb1).trans (zpowers_eq_of_prime_card hacard
      (Subgroup.mem_zpowers a) ha1).symm |>.symm
  have hnB : ∀ g, (g = a * b ∨ g = a * b * b) → g ∈ Subgroup.zpowers b → False := by
    intro g hg hgb
    apply hne
    have hamem : a ∈ Subgroup.zpowers b := by
      rcases hg with rfl | rfl
      · have h1 := Subgroup.mul_mem _ hgb (Subgroup.inv_mem _ (Subgroup.mem_zpowers b))
        have e : (a * b) * b⁻¹ = a := by group
        rwa [e] at h1
      · have h1 := Subgroup.mul_mem _ hgb (Subgroup.inv_mem _ (Subgroup.mem_zpowers b))
        have h2 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (Subgroup.mem_zpowers b))
        have e : (a * b * b) * b⁻¹ * b⁻¹ = a := by group
        rwa [e] at h2
    exact (zpowers_eq_of_prime_card hbcard hamem ha1).trans (zpowers_eq_of_prime_card hbcard
      (Subgroup.mem_zpowers b) hb1).symm
  have hgP : ∀ g, (g = a * b ∨ g = a * b * b) → Subgroup.zpowers g ≤ pCoreOf 3 X := by
    intro g hg
    refine Subgroup.zpowers_le.mpr ?_
    rcases hg with rfl | rfl
    · exact (pCoreOf 3 X).mul_mem haP hbP
    · exact (pCoreOf 3 X).mul_mem ((pCoreOf 3 X).mul_mem haP hbP) hbP
  have hdiag : ∀ g, (g = a * b ∨ g = a * b * b) → orderOf g = 3 →
      (Subgroup.zpowers g ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers u) = ⊥ ∧
        Subgroup.zpowers g ⊓ (Subgroup.zpowers b ⊔ Subgroup.zpowers t) = ⊥) := by
    intro g hg hgo
    have hgcard : Nat.card (Subgroup.zpowers g) = 3 := by rw [Nat.card_zpowers, hgo]
    have hga : Subgroup.zpowers g ⊓ Subgroup.zpowers a = ⊥ := by
      apply inf_eq_bot_of_card_prime hgcard hacard
      intro heq
      exact hnA g hg (heq ▸ Subgroup.mem_zpowers g)
    have hgb : Subgroup.zpowers g ⊓ Subgroup.zpowers b = ⊥ := by
      apply inf_eq_bot_of_card_prime hgcard hbcard
      intro heq
      exact hnB g hg (heq ▸ Subgroup.mem_zpowers g)
    constructor
    · rw [eq_bot_iff]
      rintro x ⟨hxg, hxL⟩
      have : x ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers u) ⊓ pCoreOf 3 X := ⟨hxL, hgP g hg hxg⟩
      rw [hP1] at this
      rw [← hga]
      exact ⟨hxg, this⟩
    · rw [eq_bot_iff]
      rintro x ⟨hxg, hxL⟩
      have : x ∈ (Subgroup.zpowers b ⊔ Subgroup.zpowers t) ⊓ pCoreOf 3 X := ⟨hxL, hgP g hg hxg⟩
      rw [hP2] at this
      rw [← hgb]
      exact ⟨hxg, this⟩
  refine ⟨Subgroup.zpowers a ⊔ Subgroup.zpowers u, Subgroup.zpowers b ⊔ Subgroup.zpowers t, hcomm,
    ?_, ?_, hD1, hD2, hdiag (a * b) (Or.inl rfl) hoc, hdiag (a * b * b) (Or.inr rfl) hoc'⟩
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hxa : x ∈ Subgroup.zpowers a := by
      refine mem_zpowers_of_commute hao k.hb2 hinvA hx1 ?_
      exact hcomm a (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) x hx2
    have hxb : x ∈ Subgroup.zpowers b := by
      refine mem_zpowers_of_commute hbo k.ha2 hinvB hx2 ?_
      exact (hcomm x hx1 b (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))).symm
    have : x ∈ centR X t ⊓ centR X u := ⟨haz ▸ hxa, hbz ▸ hxb⟩
    rwa [centR_inf_eq_bot hV h k] at this
  · apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left haP)
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right k.hb)
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hbP)
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right k.ha)
    · refine sup_le ?_ ?_
      · have hPsup : pCoreOf 3 X = centR X t ⊔ centR X u := by
          rw [pCoreOf_eq_sup_triple hV h k.toTriple, h3, sup_bot_eq]
        rw [hPsup, ← haz, ← hbz]
        exact sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_left)
      · intro g hg
        rcases k.mem g hg with h' | h' | h' | h'
        · rw [h']; exact Subgroup.one_mem _
        · rw [h']
          exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
        · rw [h']
          exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
        · rw [h']
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_right
            (Subgroup.mem_zpowers t))) (Subgroup.mem_sup_left (Subgroup.mem_sup_right
            (Subgroup.mem_zpowers u)))

end Two

end CFSG.Quasithin
