module

public import CFSG.Quasithin.Recognition.HSType17d
public import CFSG.Quasithin.Recognition.HSTypeStar
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem nonempty_closure_equiv_dihedral {G : Type*} [Group G] [Finite G] {r s : G}
    (hr : orderOf r = 4) (hs : s * s = 1) (hrel : s * r * s⁻¹ = r⁻¹)
    (hsr : s ∉ Subgroup.zpowers r) :
    Nonempty (↥(Subgroup.closure ({r, s} : Set G)) ≃* DihedralGroup 4) := by
  set D := Subgroup.closure ({r, s} : Set G)
  have hrD : r ∈ D := Subgroup.subset_closure (Set.mem_insert _ _)
  have hsD : s ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  let ρ : D := ⟨r, hrD⟩
  let σ : D := ⟨s, hsD⟩
  have hgen : ⊤ = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype, Subgroup.map_sup,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    show Subgroup.closure ({r, s} : Set G) = Subgroup.zpowers r ⊔ Subgroup.zpowers s
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Set.insert_eq]
  have hσ2 : σ ^ 2 = 1 := Subtype.ext (by simp [σ, pow_two, hs])
  have hrel' : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (by simpa [σ, ρ] using hrel)
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro hm
    apply hsr
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa [σ, ρ] using congrArg Subtype.val hk⟩
  have hρ4 : orderOf ρ = 4 := by rw [← Subgroup.orderOf_coe]; exact hr
  have := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel' hσρ
  rwa [hρ4] at this


theorem mem_closure_dihedral {G : Type*} [Group G] {r s : G} (hs : s * s = 1)
    (hrel : s * r * s⁻¹ = r⁻¹) {d : G} (hd : d ∈ Subgroup.closure ({r, s} : Set G)) :
    ∃ k : ℤ, d = r ^ k ∨ d = s * r ^ k := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs
  have hconj : ∀ a : ℤ, r ^ a * s = s * r ^ (-a) := by
    intro a
    have : s * r ^ (-a) * s⁻¹ = r ^ a := by
      rw [← conj_zpow, hrel, inv_zpow', neg_neg]
    calc r ^ a * s = s * r ^ (-a) * s⁻¹ * s := by rw [this]
      _ = s * r ^ (-a) := by group
  induction hd using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, Or.inl (zpow_one _).symm⟩
    · exact ⟨0, Or.inr (by rw [zpow_zero, mul_one])⟩
  | one => exact ⟨0, Or.inl (zpow_zero _).symm⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨a, ha | ha⟩ := ihx <;> obtain ⟨b, hb | hb⟩ := ihy <;> subst ha <;> subst hb
    · exact ⟨a + b, Or.inl (zpow_add _ _ _).symm⟩
    · refine ⟨b - a, Or.inr ?_⟩
      rw [← mul_assoc, hconj, mul_assoc, ← zpow_add, neg_add_eq_sub]
    · refine ⟨a + b, Or.inr ?_⟩
      rw [mul_assoc, ← zpow_add]
    · refine ⟨b - a, Or.inl ?_⟩
      rw [mul_assoc, ← mul_assoc (r ^ a), hconj, mul_assoc, ← zpow_add, ← mul_assoc, hs,
        one_mul, neg_add_eq_sub]
  | inv x _ ih =>
    obtain ⟨a, ha | ha⟩ := ih <;> subst ha
    · exact ⟨-a, Or.inl (zpow_neg r a).symm⟩
    · refine ⟨a, Or.inr ?_⟩
      rw [mul_inv_rev, hsinv, ← zpow_neg, hconj, neg_neg]

namespace HSSetting

variable {G : Type} [Group G] {z : G} {V : Subgroup G}

theorem isConj_of_mem_A {A : Subgroup G} (e : ↥A ≃* alternatingGroup (Fin 5)) {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hb2 : b * b = 1) (hb1 : b ≠ 1) :
    ∃ g ∈ A, g * a * g⁻¹ = b := by
  have key : ∀ (c : G) (hc : c ∈ A), c * c = 1 → c ≠ 1 →
      ∃ g ∈ A, g * c * g⁻¹ = (e.symm ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide⟩ : G) := by
    intro c hc hc2 hc1
    set σ : Equiv.Perm (Fin 5) := (e ⟨c, hc⟩ : Equiv.Perm (Fin 5)) with hσ
    have hσ2 : σ * σ = 1 := by
      rw [hσ, ← Subgroup.coe_mul, ← map_mul]
      have : (⟨c, hc⟩ : ↥A) * ⟨c, hc⟩ = 1 := Subtype.ext hc2
      rw [this, map_one]; rfl
    have hσ1 : σ ≠ 1 := by
      intro h1
      apply hc1
      have : e ⟨c, hc⟩ = 1 := Subtype.ext h1
      have := congrArg Subtype.val (e.injective (this.trans (map_one e).symm))
      exact this
    have hσs : Equiv.Perm.sign σ = 1 := (e ⟨c, hc⟩).2
    obtain ⟨ρ, hρs, hρ⟩ := alt_five_invol_conj σ hσs hσ2 hσ1
    refine ⟨(e.symm ⟨ρ, hρs⟩ : G), (e.symm ⟨ρ, hρs⟩).2, ?_⟩
    have e1 : (e.symm ⟨ρ, hρs⟩ : ↥A) * ⟨c, hc⟩ * (e.symm ⟨ρ, hρs⟩)⁻¹ =
        e.symm ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide⟩ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, e.apply_symm_apply, e.apply_symm_apply]
      exact Subtype.ext (by simpa [hσ] using hρ)
    have := congrArg Subtype.val e1
    simpa using this
  obtain ⟨g₁, hg₁A, hg₁⟩ := key a ha ha2 ha1
  obtain ⟨g₂, hg₂A, hg₂⟩ := key b hb hb2 hb1
  refine ⟨g₂⁻¹ * g₁, A.mul_mem (A.inv_mem hg₂A) hg₁A, ?_⟩
  calc g₂⁻¹ * g₁ * a * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * a * g₁⁻¹) * g₂ := by group
    _ = g₂⁻¹ * (g₂ * b * g₂⁻¹) * g₂ := by rw [hg₁, hg₂]
    _ = b := by group

theorem exists_D [Finite G] (h : HSSetting z V) {t : G} (htK : t ∈ hsK z) (htQ : t ∉ hsQ z)
    (htt : t * t = 1) (htz : ∀ g : G, g * z * g⁻¹ ≠ t) {A : Subgroup G}
    (hAt : A ≤ Subgroup.centralizer ({t} : Set G)) (eA : ↥A ≃* alternatingGroup (Fin 5))
    (hzA : z ∈ A)
    (hAX : A ≤ opResidual 2 (Subgroup.centralizer ({t} : Set G)))
    {s : G} (hsA : s ∈ A) (hss : s * s = 1) (hs1 : s ≠ 1) (hsz : s ≠ z) (hszc : s * z = z * s)
    (hsK : s ∉ hsK z) {φ : ↥(hsH z) →* Equiv.Perm (Fin 5)}
    (hker : φ.ker = (hsQ z).subgroupOf (hsH z)) (hφt : φ ⟨t, htK.1⟩ = t₅)
    (hsmemH : s ∈ hsH z) (hφs : φ ⟨s, hsmemH⟩ = Equiv.swap 0 1) :
    ∃ D : Subgroup G, Nonempty (↥D ≃* DihedralGroup 4) ∧ Nat.card D = 8 ∧
      D ≤ sPrime φ t ∧ D ≤ opResidual 2 (Subgroup.centralizer ({t} : Set G)) ∧ t ∉ D ∧
      (∀ d ∈ D, d * d = 1 → d ≠ 1 →
        ∃ g ∈ Subgroup.centralizer ({t} : Set G), g * z * g⁻¹ = d) ∧
      ∀ d ∈ D, d * d ≠ 1 → d * d = z := by
  classical
  set C := Subgroup.centralizer ({t} : Set G) with hC
  have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp (hAt hsA)
  have hzz : z * z = 1 := h.z_mul_z
  have hmem : ∀ a : ↥(hsH z), φ a = 1 ↔ (a : G) ∈ hsQ z := fun a => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  obtain ⟨y, hyT, hφy⟩ := h.exists_mem_T_of_comm htK htQ htt hker hφt swap02_comm_t5
  have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyT.2
  set s' := y * s * y⁻¹ with hs'
  have hs'H : s' ∈ hsH z := (hsH z).mul_mem ((hsH z).mul_mem hyT.1 hsmemH) ((hsH z).inv_mem hyT.1)
  have hφs' : φ ⟨s', hs'H⟩ = Equiv.swap 2 3 := by
    rw [show (⟨s', hs'H⟩ : ↥(hsH z)) = ⟨y, hyT.1⟩ * ⟨s, hsmemH⟩ * (⟨y, hyT.1⟩)⁻¹ from rfl,
      map_mul, map_mul, map_inv, hφy, hφs]
    exact conj_swap01_of_not_inV5 _ swap02_comm_t5 not_inV5_swap02
  have hs't : s' * t = t * s' := by
    rw [hs']
    calc y * s * y⁻¹ * t = y * s * (y⁻¹ * t) := by group
      _ = y * s * (t * y⁻¹) := by
          rw [show y⁻¹ * t = t * y⁻¹ by
            calc y⁻¹ * t = y⁻¹ * (t * y) * y⁻¹ := by group
              _ = y⁻¹ * (y * t) * y⁻¹ := by rw [hyt]
              _ = t * y⁻¹ := by group]
      _ = y * (s * t) * y⁻¹ := by group
      _ = y * (t * s) * y⁻¹ := by rw [hst]
      _ = (y * t) * s * y⁻¹ := by group
      _ = (t * y) * s * y⁻¹ := by rw [hyt]
      _ = t * (y * s * y⁻¹) := by group
  have hs's' : s' * s' = 1 := by
    rw [hs']
    calc y * s * y⁻¹ * (y * s * y⁻¹) = y * (s * s) * y⁻¹ := by group
      _ = 1 := by rw [hss]; group
  set r := s * s' with hr
  have hrH : r ∈ hsH z := (hsH z).mul_mem hsmemH hs'H
  have hφr : φ ⟨r, hrH⟩ = φ ⟨t, htK.1⟩ := by
    rw [show (⟨r, hrH⟩ : ↥(hsH z)) = ⟨s, hsmemH⟩ * ⟨s', hs'H⟩ from rfl, map_mul, hφs, hφs', hφt]
  have hq : t⁻¹ * r ∈ hsQ z := by
    have : φ ⟨t⁻¹ * r, (hsH z).mul_mem ((hsH z).inv_mem htK.1) hrH⟩ = 1 := by
      rw [show (⟨t⁻¹ * r, _⟩ : ↥(hsH z)) = (⟨t, htK.1⟩)⁻¹ * ⟨r, hrH⟩ from rfl, map_mul, map_inv,
        hφr, inv_mul_cancel]
    exact (hmem _).mp this
  have hrt : r * t = t * r := by
    rw [hr]
    calc s * s' * t = s * (s' * t) := by group
      _ = s * (t * s') := by rw [hs't]
      _ = (s * t) * s' := by group
      _ = (t * s) * s' := by rw [hst]
      _ = t * (s * s') := by group
  set q := t⁻¹ * r with hqdef
  have hqt : q * t = t * q := by
    rw [hqdef]
    calc t⁻¹ * r * t = t⁻¹ * (r * t) := by group
      _ = t⁻¹ * (t * r) := by rw [hrt]
      _ = r := by group
      _ = t * (t⁻¹ * r) := by group
  have hrq : r = t * q := by rw [hqdef]; group
  have hr2 : r * r = q * q := by
    rw [hrq]
    calc t * q * (t * q) = t * (q * t) * q := by group
      _ = t * (t * q) * q := by rw [hqt]
      _ = (t * t) * (q * q) := by group
      _ = q * q := by rw [htt, one_mul]
  have hzA1 : z ≠ 1 := h.z_ne_one
  obtain ⟨g₁, hg₁A, hg₁⟩ := isConj_of_mem_A eA hzA hsA hzz hzA1 hss hs1
  have hsz' : IsConj z s := isConj_iff.mpr ⟨g₁, hg₁⟩
  have hs'z : IsConj z s' := hsz'.trans (isConj_iff.mpr ⟨y, rfl⟩)
  have hss'1 : s * s' ≠ 1 := by
    intro h1
    have : s' = s := by
      calc s' = s * (s * s') := by rw [← mul_assoc, hss, one_mul]
        _ = s := by rw [h1, mul_one]
    have e := congrArg φ (show (⟨s', hs'H⟩ : ↥(hsH z)) = ⟨s, hsmemH⟩ from Subtype.ext this)
    rw [hφs', hφs] at e
    exact absurd e (by decide)
  have hr2z : r * r = z := by
    rcases h.mul_self_eq_one_or_z hq with h1 | h1
    · exfalso
      have hcomm : s * s' = s' * s := by
        have h2 : r * r = 1 := by rw [hr2, h1]
        rw [hr] at h2
        calc s * s' = s * s' * (s * s') * (s' * s) := by
              rw [show s * s' * (s * s') * (s' * s) = s * s' * s * (s' * s') * s by group, hs's',
                mul_one, mul_assoc, hss, mul_one]
          _ = s' * s := by rw [h2, one_mul]
      have hrz : IsConj z r := h.star s s' hsz' hs'z hcomm hss'1
      by_cases hq1 : q = 1
      · apply htz 1
        rw [show t = r by rw [hrq, hq1, mul_one]]
        obtain ⟨c, hc⟩ := isConj_iff.mp hrz
        exact absurd hc (fun hc' => htz c (by rw [hc', hrq, hq1, mul_one]))
      · have hqZ : q ∉ hsZQ z ∨ q = z := by
          by_cases hqZ : q ∈ hsZQ z
          · right; exact h.eq_z_of_mem_ZQ hqZ h1 hq1
          · left; exact hqZ
        have hqz : IsConj z q := by
          rcases hqZ with hqZ | rfl
          · obtain ⟨c, hc⟩ := h.exists_conj_z_of_invol_Q hq h1 hqZ
            exact isConj_iff.mpr ⟨c, hc⟩
          · exact IsConj.refl _
        have hrqc : r * q = q * r := by
          rw [hrq]
          calc t * q * q = t * (q * q) := by group
            _ = q * (t * q) := by rw [h1, mul_one]; rw [← hqt]; group; rw [h1]; group
        have hrq1 : r * q ≠ 1 := by
          rw [hrq, mul_assoc, h1, mul_one]
          exact fun h1 => htQ (h1 ▸ (hsQ z).one_mem)
        have := h.star r q hrz hqz hrqc hrq1
        obtain ⟨c, hc⟩ := isConj_iff.mp this
        apply htz c
        rw [hc, hrq, mul_assoc, h1, mul_one]
    · rw [hr2, h1]
  have hr4 : r ^ 4 = 1 := by
    have e4 : r ^ 4 = (r ^ 2) ^ 2 := by rw [← pow_mul]
    rw [e4, sq r, hr2z, sq, hzz]
  have hro : orderOf r = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h44 : r ^ 2 ^ (1 + 1) = 1 := by norm_num [hr4]
    have h2 : ¬ r ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq, hr2z]
      exact h.z_ne_one
    have := orderOf_eq_prime_pow h2 h44
    norm_num at this
    exact this
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  have hs'inv : s'⁻¹ = s' := inv_eq_of_mul_eq_one_left hs's'
  have hrel : s * r * s⁻¹ = r⁻¹ := by
    rw [hr, hsinv, mul_inv_rev, hsinv, hs'inv, ← mul_assoc, hss, one_mul]
  have hs'1 : s' ≠ 1 := fun h1 => hs1 (by
    calc s = y⁻¹ * s' * y := by rw [hs']; group
      _ = 1 := by rw [h1]; group)
  have hrz : r * r = z := hr2z
  have hzc : ∀ g ∈ hsH z, g * z = z * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have hrk : ∀ k : ℤ, r ^ k = 1 ∨ r ^ k = r ∨ r ^ k = z ∨ r ^ k = r⁻¹ := by
    intro k
    have hk : r ^ k = r ^ (k % 4) := by
      rw [← zpow_mod_orderOf, hro]; rfl
    rw [hk]
    have h0 : 0 ≤ k % 4 := Int.emod_nonneg k (by norm_num)
    have h4 : k % 4 < 4 := Int.emod_lt_of_pos k (by norm_num)
    interval_cases (k % 4)
    · left; simp
    · right; left; simp
    · right; right; left; rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, sq, hr2z]
    · right; right; right
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, eq_inv_iff_mul_eq_one,
        ← pow_succ, hr4]
  have hsX : s ∉ Subgroup.zpowers r := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    rcases hrk k with h1 | h1 | h1 | h1 <;> rw [h1] at hk
    · exact hs1 hk.symm
    · apply hs'1
      have : s * s' = s := hk
      calc s' = s * (s * s') := by rw [← mul_assoc, hss, one_mul]
        _ = 1 := by rw [this, hss]
    · exact hsz hk.symm
    · apply hs'1
      have : (s * s')⁻¹ = s := hk
      rw [mul_inv_rev, hsinv, hs'inv] at this
      calc s' = s' * s * s := by rw [mul_assoc, hss, mul_one]
        _ = 1 := by rw [this, hss]
  set D := Subgroup.closure ({r, s} : Set G) with hD
  obtain ⟨eD⟩ := nonempty_closure_equiv_dihedral hro hss hrel hsX
  have hDcard : Nat.card D = 8 := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
  have hsS : s ∈ sPrime φ t := ⟨hAt hsA, hsmemH, by rw [hφs]; exact inV5_swap01⟩
  have hs'S : s' ∈ sPrime φ t :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hs't, hs'H, by rw [hφs']; decide⟩
  have hXn : ∀ g ∈ C, ∀ x ∈ opResidual 2 C, g * x * g⁻¹ ∈ opResidual 2 C := by
    intro g hg x hx
    have hn := (opResidual_normal 2 C).conj_mem ⟨x, opResidual_le 2 C hx⟩ hx ⟨g, hg⟩
    exact hn
  have hsXr : s ∈ opResidual 2 C := hAX hsA
  have hs'X : s' ∈ opResidual 2 C := hXn y hyT.2 s hsXr
  obtain ⟨g₂, hg₂A, hg₂⟩ : ∃ g ∈ A, g * z * g⁻¹ = s * z := by
    have hszA : s * z ∈ A := A.mul_mem hsA hzA
    have hsz2 : s * z * (s * z) = 1 := by
      calc s * z * (s * z) = s * (z * s) * z := by group
        _ = s * (s * z) * z := by rw [hszc]
        _ = 1 := by rw [← mul_assoc, hss, one_mul, hzz]
    have hsz1 : s * z ≠ 1 := fun h1 => hsz (by
      calc s = s * z * z := by rw [mul_assoc, hzz, mul_one]
        _ = z := by rw [h1, one_mul])
    exact isConj_of_mem_A eA hzA hszA hzz hzA1 hsz2 hsz1
  have hyz : y * z = z * y := hzc y hyT.1
  have hs'r : s' = s * r := by rw [hr, ← mul_assoc, hss, one_mul]
  have hr3 : r * (r * r) = r⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc r * (r * r) * r = r ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hr4
  have hinvD : ∀ d ∈ D, d * d = 1 → d ≠ 1 → ∃ g ∈ C, g * z * g⁻¹ = d := by
    intro d hd hd2 hd1
    obtain ⟨k, hk | hk⟩ := mem_closure_dihedral hss hrel hd <;> subst hk
    · rcases hrk k with h1 | h1 | h1 | h1 <;> rw [h1] at hd2 hd1 ⊢
      · exact absurd rfl hd1
      · exfalso; rw [hrz] at hd2; exact h.z_ne_one hd2
      · exact ⟨1, C.one_mem, by group⟩
      · exfalso
        rw [← mul_inv_rev, inv_eq_one, hrz] at hd2
        exact h.z_ne_one hd2
    · rcases hrk k with h1 | h1 | h1 | h1 <;> rw [h1]
      · exact ⟨g₁, hAt hg₁A, by rw [hg₁, mul_one]⟩
      · refine ⟨y * g₁, C.mul_mem hyT.2 (hAt hg₁A), ?_⟩
        rw [← hs'r]
        calc y * g₁ * z * (y * g₁)⁻¹ = y * (g₁ * z * g₁⁻¹) * y⁻¹ := by group
          _ = s' := by rw [hg₁]
      · exact ⟨g₂, hAt hg₂A, hg₂⟩
      · refine ⟨y * g₂, C.mul_mem hyT.2 (hAt hg₂A), ?_⟩
        calc y * g₂ * z * (y * g₂)⁻¹ = y * (g₂ * z * g₂⁻¹) * y⁻¹ := by group
          _ = y * (s * z) * y⁻¹ := by rw [hg₂]
          _ = (y * s * y⁻¹) * (y * z * y⁻¹) := by group
          _ = s' * z := by rw [← hs', hyz, mul_inv_cancel_right]
          _ = s * r * (r * r) := by rw [hs'r, hrz]
          _ = s * r⁻¹ := by rw [mul_assoc, hr3]
  have hsqD : ∀ d ∈ D, d * d ≠ 1 → d * d = z := by
    intro d hd hd2
    obtain ⟨k, hk | hk⟩ := mem_closure_dihedral hss hrel hd <;> subst hk
    · rcases hrk k with h1 | h1 | h1 | h1 <;> rw [h1] at hd2 ⊢
      · exact absurd (mul_one 1) hd2
      · exact hrz
      · exact absurd hzz hd2
      · rw [← mul_inv_rev, hrz, inv_eq_of_mul_eq_one_left hzz]
    · exfalso
      apply hd2
      have e := (congrArg (fun w => s * w * s⁻¹) (rfl : r ^ k = r ^ k))
      have hconjk : s * r ^ k * s⁻¹ = (r ^ k)⁻¹ := by rw [← conj_zpow, hrel, inv_zpow]
      calc s * r ^ k * (s * r ^ k) = (s * r ^ k * s⁻¹) * (s * s) * r ^ k := by group
        _ = 1 := by rw [hconjk, hss, mul_one, inv_mul_cancel]
  have hDS : D ≤ sPrime φ t := by
    rw [hD, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact (sPrime φ t).mul_mem hsS hs'S
    · exact hsS
  have hDX : D ≤ opResidual 2 C := by
    rw [hD, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact (opResidual 2 C).mul_mem hsXr hs'X
    · exact hsXr
  have htD : t ∉ D := by
    intro htD
    obtain ⟨g, -, hg⟩ := hinvD t htD htt (fun h1 => htQ (h1 ▸ (hsQ z).one_mem))
    exact htz g hg
  exact ⟨D, ⟨eD⟩, hDcard, hDS, hDX, htD, hinvD, hsqD⟩

end HSSetting

end CFSG.Quasithin.HSType
