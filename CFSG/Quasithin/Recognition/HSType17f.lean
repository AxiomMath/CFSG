module

public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Quasithin.Background.A1cBridge
public import CFSG.Quasithin.Recognition.HSType17d
public import CFSG.Quasithin.Recognition.HSTypeStar

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Transfer

variable {G : Type*} [Group G]

theorem zmod2_mul_self : ∀ u : Multiplicative (ZMod 2), u * u = 1 := by decide

theorem zmod2_eq_one_or : ∀ a b : Multiplicative (ZMod 2), b ≠ 1 → a = 1 ∨ a = b := by decide

theorem zmod2_pow_odd (u : Multiplicative (ZMod 2)) {n : ℕ} (hn : ¬ 2 ∣ n) : u ^ n = u := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  rw [pow_succ, pow_mul, sq, zmod2_mul_self, one_pow, one_mul]

theorem exists_transfer_hom [Finite G] {X P K : Subgroup G} (hPX : P ≤ X)
    (hodd : ¬ 2 ∣ P.relIndex X)
    (hK2 : ∀ a ∈ P, ∀ b ∈ P, a * b ∈ K ↔ (a ∈ K ↔ b ∈ K)) :
    ∃ f : ↥X →* Multiplicative (ZMod 2),
      (∀ x : ↥X, ¬ 2 ∣ orderOf x → f x = 1) ∧
      ∀ g (hg : g ∈ P), (∀ k : ℕ, ∀ a ∈ X, a⁻¹ * g ^ k * a ∈ P →
          (a⁻¹ * g ^ k * a ∈ K ↔ g ^ k ∈ K)) → (f ⟨g, hPX hg⟩ = 1 ↔ g ∈ K) := by
  classical
  set H := P.subgroupOf X with hH
  have hKone : (1 : G) ∈ K := K.one_mem
  let ϕf : ↥H → Multiplicative (ZMod 2) := fun h =>
    if ((h : ↥X) : G) ∈ K then 1 else Multiplicative.ofAdd 1
  have hϕf : ∀ h : ↥H, ϕf h = 1 ↔ ((h : ↥X) : G) ∈ K := by
    intro h
    by_cases hK : ((h : ↥X) : G) ∈ K <;> simp only [ϕf, hK] <;> decide
  have hϕf' : ∀ h : ↥H, ((h : ↥X) : G) ∉ K → ϕf h = Multiplicative.ofAdd 1 := by
    intro h hK
    simp only [ϕf, hK]
    decide
  have hϕf1 : ∀ h : ↥H, ((h : ↥X) : G) ∈ K → ϕf h = 1 := fun h hK => (hϕf h).mpr hK
  let ϕ : ↥H →* Multiplicative (ZMod 2) := MonoidHom.mk' ϕf (fun a b => by
    have ha : ((a : ↥X) : G) ∈ P := a.2
    have hb : ((b : ↥X) : G) ∈ P := b.2
    have key := hK2 _ ha _ hb
    have hab : (((a * b : ↥H) : ↥X) : G) = ((a : ↥X) : G) * ((b : ↥X) : G) := rfl
    by_cases haK : ((a : ↥X) : G) ∈ K <;> by_cases hbK : ((b : ↥X) : G) ∈ K
    · rw [hϕf1 _ (by rw [hab]; exact key.mpr (iff_of_true haK hbK)), hϕf1 _ haK, hϕf1 _ hbK,
        one_mul]
    · rw [hϕf' _ (by rw [hab]; exact fun h => hbK ((key.mp h).mp haK)), hϕf1 _ haK,
        hϕf' _ hbK, one_mul]
    · rw [hϕf' _ (by rw [hab]; exact fun h => haK ((key.mp h).mpr hbK)), hϕf' _ haK,
        hϕf1 _ hbK, mul_one]
    · rw [hϕf1 _ (by rw [hab]; exact key.mpr (iff_of_false haK hbK)), hϕf' _ haK, hϕf' _ hbK]
      decide)
  have hϕ : ∀ h : ↥H, ϕ h = 1 ↔ ((h : ↥X) : G) ∈ K := hϕf
  refine ⟨MonoidHom.transfer ϕ, ?_, ?_⟩
  · intro x hx
    have h1 : (MonoidHom.transfer ϕ x) ^ orderOf x = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have h2 : (MonoidHom.transfer ϕ x) ^ 2 = 1 := by rw [sq, zmod2_mul_self]
    have hcop : Nat.Coprime (orderOf x) 2 :=
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hx))
    have := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rwa [hcop, pow_one] at this
  · intro g hg hcond
    have hgH : (⟨g, hPX hg⟩ : ↥X) ∈ H := hg
    have hV := transfer_eq_pow_of_forall ϕ hgH (by
      intro k a ha
      have hmem : ((a⁻¹ * ⟨g, hPX hg⟩ ^ k * a : ↥X) : G) = (a : G)⁻¹ * g ^ k * a := by
        simp
      have hP' : (a : G)⁻¹ * g ^ k * a ∈ P := by rw [← hmem]; exact ha
      have hiff := hcond k a a.2 hP'
      have hk' : (((⟨⟨g, hPX hg⟩ ^ k, H.pow_mem hgH k⟩ : ↥H) : ↥X) : G) = g ^ k := by simp
      show ϕf ⟨_, ha⟩ = ϕf ⟨_, H.pow_mem hgH k⟩
      by_cases hK : g ^ k ∈ K
      · rw [hϕf1 _ (by rw [Subgroup.coe_mk, hmem]; exact hiff.mpr hK),
          hϕf1 _ (by rw [hk']; exact hK)]
      · rw [hϕf' _ (by rw [Subgroup.coe_mk, hmem]; exact fun h => hK (hiff.mp h)),
          hϕf' _ (by rw [hk']; exact hK)])
    erw [hV, zmod2_pow_odd _ hodd, hϕ]

theorem opResidual_le_ker {X Y : Subgroup G} (hYX : opResidual 2 Y ≤ X)
    (f : ↥X →* Multiplicative (ZMod 2)) (hf : ∀ x : ↥X, ¬ 2 ∣ orderOf x → f x = 1) {y : G}
    (hy : y ∈ opResidual 2 Y) : f ⟨y, hYX hy⟩ = 1 := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    refine hf _ ?_
    rw [Subgroup.orderOf_mk]
    exact fun h2 => absurd (Nat.Coprime.coprime_dvd_left h2 hx.2) (by norm_num)
  | one => exact map_one f
  | mul a b ha hb iha ihb =>
    have e : (⟨a * b, hYX (Subgroup.mul_mem _ ha hb)⟩ : ↥X) =
        ⟨a, hYX ha⟩ * ⟨b, hYX hb⟩ := rfl
    rw [e, map_mul, iha, ihb, one_mul]
  | inv a ha iha =>
    have e : (⟨a⁻¹, hYX (Subgroup.inv_mem _ ha)⟩ : ↥X) = (⟨a, hYX ha⟩)⁻¹ := rfl
    rw [e, map_inv, iha]
    exact inv_one

theorem opResidual_le_opResidual_self (Y : Subgroup G) :
    opResidual 2 Y ≤ opResidual 2 (opResidual 2 Y) := by
  rw [opResidual, Subgroup.closure_le]
  rintro x ⟨hxY, hxc⟩
  exact mem_opResidual_of_coprime (Subgroup.subset_closure ⟨hxY, hxc⟩) hxc

theorem le_normalizer_opResidual {C T : Subgroup G} (hTC : T ≤ C) :
    T ≤ Subgroup.normalizer (opResidual 2 C : Set G) := by
  have hXn : ∀ g ∈ C, ∀ x ∈ opResidual 2 C, g * x * g⁻¹ ∈ opResidual 2 C := fun g hg x hx =>
    (opResidual_normal 2 C).conj_mem ⟨x, opResidual_le 2 C hx⟩ hx ⟨g, hg⟩
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hXn g (hTC hg) x hx, fun hx => ?_⟩
  have := hXn g⁻¹ (C.inv_mem (hTC hg)) _ hx
  simpa [mul_assoc] using this

theorem opResidual_sup_eq [Finite G] {C T : Subgroup G} (hTC : T ≤ C)
    (hodd : ¬ 2 ∣ T.relIndex C) : opResidual 2 C ⊔ T = C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := opResidual 2 C with hX
  have hXC : X ≤ C := opResidual_le 2 C
  have h2pow : ∃ m : ℕ, X.relIndex C = 2 ^ m := by
    have : (X.subgroupOf C).Normal := opResidual_normal 2 C
    have hp : IsPGroup 2 (↥C ⧸ X.subgroupOf C) := by
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨k, hk⟩ := exists_pow_mem_opResidual (p := 2) (A := C) g.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hp
    exact ⟨m, by rw [Subgroup.relIndex, Subgroup.index, hm]⟩
  refine le_antisymm (sup_le hXC hTC) ?_
  have h1 : (X ⊔ T).relIndex C ∣ T.relIndex C := Subgroup.relIndex_dvd_of_le_left _ le_sup_right
  have h2 : (X ⊔ T).relIndex C ∣ X.relIndex C := Subgroup.relIndex_dvd_of_le_left _ le_sup_left
  obtain ⟨m, hm⟩ := h2pow
  rw [hm] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have : (X ⊔ T).relIndex C = 1 := by
    rcases j with _ | j
    · simpa using hj
    · exfalso
      apply hodd
      rw [hj] at h1
      exact (dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h1
  exact Subgroup.relIndex_eq_one.mp this

end Transfer

section DT

variable {G : Type*} [Group G]

@[expose] def dPlusT (D : Subgroup G) {t : G} (htt : t * t = 1)
    (htD : ∀ d ∈ D, d * t = t * d) : Subgroup G where
  carrier := {w | w ∈ D ∨ t * w ∈ D}
  mul_mem' := by
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (D.mul_mem ha hb)
    · right
      have e : t * (a * b) = a * (t * b) := by
        rw [← mul_assoc, ← mul_assoc, htD a ha]
      rw [e]; exact D.mul_mem ha hb
    · right
      rw [← mul_assoc]; exact D.mul_mem ha hb
    · left
      have hat : (t * a) * t = t * (t * a) := htD _ ha
      have e : a * b = (t * a) * (t * b) := by
        calc a * b = (t * t) * a * b := by rw [htt, one_mul]
          _ = t * (t * a) * b := by group
          _ = (t * a) * t * b := by rw [← hat]
          _ = (t * a) * (t * b) := by group
      rw [e]; exact D.mul_mem ha hb
  one_mem' := Or.inl D.one_mem
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (D.inv_mem ha)
    · right
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
      have hat' : a * t = t * a := by
        have h3 := htD _ ha
        calc a * t = t⁻¹ * ((t * a) * t) := by group
          _ = t⁻¹ * (t * (t * a)) := by rw [h3]
          _ = t * a := by group
      have e : t * a⁻¹ = (t * a)⁻¹ := by
        rw [mul_inv_rev, htinv]
        calc t * a⁻¹ = a⁻¹ * (a * t) * a⁻¹ := by group
          _ = a⁻¹ * (t * a) * a⁻¹ := by rw [hat']
          _ = a⁻¹ * t := by group
      rw [e]; exact D.inv_mem ha

end DT

namespace HSSetting

variable {G : Type} [Group G] {z : G} {V : Subgroup G}

theorem inf_T_eq_D [Finite G] (h : HSSetting z V) {t : G} (htK : t ∈ hsK z) (htQ : t ∉ hsQ z)
    (htt : t * t = 1) (htz : ∀ g : G, g * z * g⁻¹ ≠ t) {φ : ↥(hsH z) →* Equiv.Perm (Fin 5)}
    (hker : φ.ker = (hsQ z).subgroupOf (hsH z)) (hφt : φ ⟨t, htK.1⟩ = t₅)
    {s : G} (hsmemH : s ∈ hsH z) (hsK : s ∉ hsK z) (hss : s * s = 1) (hst : s * t = t * s)
    (hφs : φ ⟨s, hsmemH⟩ = Equiv.swap 0 1)
    {D : Subgroup G} (hDcard : Nat.card D = 8) (hDS : D ≤ sPrime φ t)
    (hDX : D ≤ opResidual 2 (Subgroup.centralizer ({t} : Set G))) (htD : t ∉ D)
    (hinvD : ∀ d ∈ D, d * d = 1 → d ≠ 1 →
      ∃ g ∈ Subgroup.centralizer ({t} : Set G), g * z * g⁻¹ = d)
    {v : G} (hvT : v ∈ hsH z ⊓ Subgroup.centralizer ({t} : Set G)) (hvz : IsConj z v)
    (hvII : ∀ g ∈ Subgroup.centralizer ({t} : Set G), g * z * g⁻¹ ≠ v)
    {e : G} (heT : e ∈ hsH z ⊓ Subgroup.centralizer ({t} : Set G)) (heS : e ∉ sPrime φ t)
    (he4 : e ^ 4 = 1) (hez : IsConj z (e * e))
    (he2 : e * e = z ∨ ∀ g ∈ Subgroup.centralizer ({t} : Set G), g * z * g⁻¹ ≠ e * e) :
    opResidual 2 (Subgroup.centralizer ({t} : Set G)) ⊓
        (hsH z ⊓ Subgroup.centralizer ({t} : Set G)) = D ∧
      Nat.card (Subgroup.centralizer ({t} : Set G)) =
        8 * Nat.card (opResidual 2 (Subgroup.centralizer ({t} : Set G))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({t} : Set G) with hC
  set T := hsH z ⊓ C with hT
  set S := sPrime φ t with hS
  set X := opResidual 2 C with hX
  have hTC : T ≤ C := inf_le_right
  have hST : S ≤ T := sPrime_le_T
  have hXC : X ≤ C := opResidual_le 2 C
  have ht1 : t ≠ 1 := fun h1 => htQ (h1 ▸ (hsQ z).one_mem)
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcen : ∀ a ∈ C, a * t = t * a := fun a ha => Subgroup.mem_centralizer_singleton_iff.mp ha
  have hT64 : Nat.card T = 64 := h.card_centralizer_H_of_invol_K htK htQ htt
  have hodd : ¬ 2 ∣ T.relIndex C := h.not_two_dvd_relIndex_T htK htQ htt htz
  have hK2 : ∀ a ∈ T, ∀ b ∈ T, a * b ∈ S ↔ (a ∈ S ↔ b ∈ S) := fun a ha b hb =>
    mem_sPrime_mul_iff htK hφt ha hb
  have hSn : ∀ a ∈ T, ∀ x ∈ T, a⁻¹ * x * a ∈ S ↔ x ∈ S := by
    intro a ha x hx
    have ha' : a⁻¹ ∈ T := T.inv_mem ha
    rw [hK2 _ (T.mul_mem ha' hx) _ ha, hK2 _ ha' _ hx]
    have : a⁻¹ ∈ S ↔ a ∈ S := ⟨fun h1 => by simpa using S.inv_mem h1, fun h1 => S.inv_mem h1⟩
    rw [this]
    tauto
  have hzS : ∀ u ∈ T, IsConj z u → u ∈ S := fun u hu huz =>
    h.mem_sPrime_of_isConj htK hker hφt hu huz
  have hsqS : ∀ y ∈ S, y * y = 1 ∨ y * y = z := fun y hy =>
    h.sq_mem_sPrime htK htQ htt hker hφt hsmemH hsK hss hst hφs hy
  have htS : t ∈ S := t_mem_sPrime htK hφt
  have hvS : v ∈ S := hzS v hvT hvz
  have hvv : v * v = 1 := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hvz
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.z_mul_z]; group
  have hee1 : e * e ≠ 1 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hez
    intro h1
    apply h.z_ne_one
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [hg, h1]; group
  have he2S : e * e ∈ S := hzS _ (T.mul_mem heT heT) hez
  have hepow : ∀ k : ℕ, e ^ k = e ^ (k % 4) := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod k 4, pow_add, pow_mul, he4, one_pow, one_mul]
  have he3S : e ^ 3 ∉ S := by
    intro h3
    apply heS
    have : e = (e ^ 3)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ', he4]
    rw [this]
    exact S.inv_mem h3
  obtain ⟨fe, hfe_odd, hfe⟩ := exists_transfer_hom hTC hodd hK2
  have hfee : fe ⟨e, hTC heT⟩ ≠ 1 := by
    intro h1
    apply heS
    refine (hfe e heT ?_).mp h1
    intro k a ha hconj
    rw [hepow k] at hconj ⊢
    have hk4 : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases (k % 4)
    · simp only [pow_zero, mul_one, inv_mul_cancel, S.one_mem]
    ·
      rw [pow_one] at hconj ⊢
      refine iff_of_false (fun hS' => ?_) heS
      rcases hsqS _ hS' with h1 | h1
      · apply hee1
        calc e * e = a * (a⁻¹ * e * a * (a⁻¹ * e * a)) * a⁻¹ := by group
          _ = 1 := by rw [h1]; group
      · rcases he2 with he2 | he2
        ·
          have haz : a * z * a⁻¹ = z := by
            calc a * z * a⁻¹ = a * (a⁻¹ * e * a * (a⁻¹ * e * a)) * a⁻¹ := by rw [h1]
              _ = e * e := by group
              _ = z := he2
          have haT : a ∈ T := ⟨Subgroup.mem_centralizer_singleton_iff.mpr (by
            calc a * z = a * z * a⁻¹ * a := by group
              _ = z * a := by rw [haz]), ha⟩
          exact heS ((hSn a haT e heT).mp hS')
        · apply he2 a ha
          calc a * z * a⁻¹ = a * (a⁻¹ * e * a * (a⁻¹ * e * a)) * a⁻¹ := by rw [h1]
            _ = e * e := by group
    · rw [show e ^ 2 = e * e from sq e] at hconj ⊢
      refine iff_of_true ?_ he2S
      refine hzS _ hconj ?_
      exact hez.trans (isConj_iff.mpr ⟨a⁻¹, by group⟩)
    ·
      refine iff_of_false (fun hS' => ?_) he3S
      rcases hsqS _ hS' with h1 | h1
      · apply hee1
        have e6 : e ^ 3 * e ^ 3 = e * e := by
          rw [← pow_add, show 3 + 3 = 4 + 2 by rfl, pow_add, he4, one_mul, sq]
        calc e * e = e ^ 3 * e ^ 3 := e6.symm
          _ = a * (a⁻¹ * e ^ 3 * a * (a⁻¹ * e ^ 3 * a)) * a⁻¹ := by group
          _ = 1 := by rw [h1]; group
      · have e6 : e ^ 3 * e ^ 3 = e * e := by
          rw [← pow_add, show 3 + 3 = 4 + 2 by rfl, pow_add, he4, one_mul, sq]
        have hzz' : a * z * a⁻¹ = e * e := by
          calc a * z * a⁻¹ = a * (a⁻¹ * e ^ 3 * a * (a⁻¹ * e ^ 3 * a)) * a⁻¹ := by rw [h1]
            _ = e ^ 3 * e ^ 3 := by group
            _ = e * e := e6
        rcases he2 with he2 | he2
        · have haz : a * z * a⁻¹ = z := hzz'.trans he2
          have haT : a ∈ T := ⟨Subgroup.mem_centralizer_singleton_iff.mpr (by
            calc a * z = a * z * a⁻¹ * a := by group
              _ = z * a := by rw [haz]), ha⟩
          exact he3S ((hSn a haT _ (T.pow_mem heT 3)).mp hS')
        · exact he2 a ha hzz'
  have hfet : fe ⟨t, htC⟩ = 1 := by
    refine (hfe t (hST htS) ?_).mpr htS
    intro k a ha _
    rw [show a⁻¹ * t ^ k * a = t ^ k by
      rw [mul_assoc, (Commute.pow_left (show Commute t a from (hcen a ha).symm) k).eq,
        inv_mul_cancel_left]]
  have hfev : fe ⟨v, hTC hvT⟩ = 1 := by
    refine (hfe v hvT ?_).mpr hvS
    intro k a ha hconj
    have hvk : v ^ k = 1 ∨ v ^ k = v := by
      rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · left; rw [← two_mul, pow_mul, sq, hvv, one_pow]
      · right; rw [pow_succ, pow_mul, sq, hvv, one_pow, one_mul]
    rcases hvk with h1 | h1 <;> rw [h1] at hconj ⊢
    · simp only [mul_one, inv_mul_cancel, S.one_mem]
    · refine iff_of_true (hzS _ hconj ?_) hvS
      exact hvz.trans (isConj_iff.mpr ⟨a⁻¹, by group⟩)
  have hfeX : ∀ x (hx : x ∈ X), fe ⟨x, hXC hx⟩ = 1 := fun x hx =>
    opResidual_le_ker hXC fe hfe_odd hx
  have hDC : D ≤ C := hDS.trans (hST.trans hTC)
  set DT := dPlusT D htt (fun d hd => hcen d (hDC hd)) with hDT
  have hDDT : D ≤ DT := fun d hd => Or.inl hd
  have htDT : t ∈ DT := Or.inr (by rw [htt]; exact D.one_mem)
  have hDTC : DT ≤ C := by
    rintro w (hw | hw)
    · exact hDC hw
    · have := C.mul_mem htC (hDC hw)
      rwa [← mul_assoc, htt, one_mul] at this
  have hDTS : DT ≤ S := by
    rintro w (hw | hw)
    · exact hDS hw
    · have := S.mul_mem htS (hDS hw)
      rwa [← mul_assoc, htt, one_mul] at this
  have hDTcard : Nat.card DT = 16 := by
    have hidx : (D.subgroupOf DT).index = 2 := by
      refine Subgroup.index_eq_two_iff.mpr ⟨⟨t, htDT⟩, fun b => ?_⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      have hbt : (b : G) * t = t * b := hcen _ (hDTC b.2)
      rcases b.2 with hb | hb
      · refine Or.inr ⟨hb, fun h1 => htD ?_⟩
        have := D.mul_mem (D.inv_mem hb) h1
        rwa [inv_mul_cancel_left] at this
      · exact Or.inl ⟨by rw [hbt]; exact hb, fun h1 => htD (by
          have := D.mul_mem hb (D.inv_mem h1)
          rwa [mul_inv_cancel_right] at this)⟩
    have h1 := (D.subgroupOf DT).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDDT).toEquiv, hDcard, hidx] at h1
    omega
  have hzDT : ∀ w ∈ DT, IsConj z w → ∃ g ∈ C, g * z * g⁻¹ = w := by
    intro w hw hwz
    have hw2 : w * w = 1 := by
      obtain ⟨g, rfl⟩ := isConj_iff.mp hwz
      calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [h.z_mul_z]; group
    have hw1 : w ≠ 1 := by
      obtain ⟨g, rfl⟩ := isConj_iff.mp hwz
      intro h1
      apply h.z_ne_one
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    rcases hw with hw | hw
    · exact hinvD w hw hw2 hw1
    · exfalso
      have hwt : w * t = t * w := hcen w (hDTC (Or.inr hw))
      have htw2 : t * w * (t * w) = 1 := by
        calc t * w * (t * w) = t * (w * t) * w := by group
          _ = t * (t * w) * w := by rw [hwt]
          _ = (t * t) * (w * w) := by group
          _ = 1 := by rw [htt, hw2, one_mul]
      have htw1 : t * w ≠ 1 := by
        intro h1
        have : w = t := by
          calc w = t * (t * w) := by rw [← mul_assoc, htt, one_mul]
            _ = t := by rw [h1, mul_one]
        obtain ⟨g, hg⟩ := isConj_iff.mp hwz
        exact htz g (hg.trans this)
      obtain ⟨g, -, hg⟩ := hinvD _ hw htw2 htw1
      have hcomm : t * w * w = w * (t * w) := by
        calc t * w * w = t * (w * w) := by group
          _ = (w * w) * t := by rw [hw2, mul_one, one_mul]
          _ = w * (w * t) := by group
          _ = w * (t * w) := by rw [hwt]
      have hprod : t * w * w ≠ 1 := by
        rw [mul_assoc, hw2, mul_one]; exact ht1
      have := h.star (t * w) w (isConj_iff.mpr ⟨g, hg⟩) hwz hcomm hprod
      rw [mul_assoc, hw2, mul_one] at this
      obtain ⟨c, hc⟩ := isConj_iff.mp this
      exact htz c hc
  have hvDT : v ∉ DT := fun hv => by
    obtain ⟨g, hgC, hg⟩ := hzDT v hv hvz
    exact hvII g hgC hg
  have hScard : Nat.card S = 32 := by
    have hidx : (S.subgroupOf T).index = 2 := by
      refine Subgroup.index_eq_two_iff.mpr ⟨⟨e, heT⟩, fun b => ?_⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      have := hK2 _ b.2 _ heT
      by_cases hb : (b : G) ∈ S
      · exact Or.inr ⟨hb, fun h1 => heS ((this.mp h1).mp hb)⟩
      · exact Or.inl ⟨this.mpr (iff_of_false hb heS), hb⟩
    have h1 := (S.subgroupOf T).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hST).toEquiv, hT64, hidx] at h1
    omega
  have hDTidx : (DT.subgroupOf S).index = 2 := by
    have h1 := (DT.subgroupOf S).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDTS).toEquiv, hDTcard, hScard] at h1
    omega
  have hK2' : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ DT ↔ (a ∈ DT ↔ b ∈ DT) := by
    intro a ha b hb
    have := Subgroup.mul_mem_iff_of_index_two hDTidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    simpa [Subgroup.mem_subgroupOf] using this
  have hfe_mem : ∀ x (hx : x ∈ C), fe ⟨x, hx⟩ = 1 ↔ x ∈ fe.ker.map C.subtype := by
    intro x hx
    constructor
    · intro h1; exact ⟨⟨x, hx⟩, h1, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact hy
  set N₁ := fe.ker.map C.subtype with hN₁
  have hN₁C : N₁ ≤ C := Subgroup.map_subtype_le _
  have hDTN : DT ≤ N₁ := by
    rintro w (hw | hw)
    · exact (hfe_mem w _).mp (hfeX w (hDX hw))
    · have h1 : fe ⟨t * w, C.mul_mem htC (hDTC (Or.inr hw))⟩ = 1 := hfeX _ (hDX hw)
      have e1 : (⟨t * w, C.mul_mem htC (hDTC (Or.inr hw))⟩ : ↥C) =
          ⟨t, htC⟩ * ⟨w, hDTC (Or.inr hw)⟩ :=
        rfl
      rw [e1, map_mul, hfet, one_mul] at h1
      exact (hfe_mem w _).mp h1
  have hSN : S ≤ N₁ := by
    intro x hx
    by_cases hxD : x ∈ DT
    · exact hDTN hxD
    · have hxv : x * v ∈ DT := (hK2' _ hx _ hvS).mpr (iff_of_false hxD hvDT)
      have h1 : fe ⟨x * v, hDTC hxv⟩ = 1 := (hfe_mem _ _).mpr (hDTN hxv)
      have e1 : (⟨x * v, hDTC hxv⟩ : ↥C) = ⟨x, hTC (hST hx)⟩ * ⟨v, hTC hvT⟩ := rfl
      rw [e1, map_mul, hfev, mul_one] at h1
      exact (hfe_mem x _).mp h1
  have hTN : ∀ x ∈ T, x ∈ N₁ → x ∈ S := by
    intro x hx hxN
    by_contra hxS
    have hxe : x * e ∈ S := (hK2 _ hx _ heT).mpr (iff_of_false hxS heS)
    have h1 : fe ⟨x * e, hTC (T.mul_mem hx heT)⟩ = 1 := (hfe_mem _ _).mpr (hSN hxe)
    have e1 : (⟨x * e, hTC (T.mul_mem hx heT)⟩ : ↥C) = ⟨x, hTC hx⟩ * ⟨e, hTC heT⟩ := rfl
    rw [e1, map_mul, (hfe_mem x _).mpr hxN, one_mul] at h1
    exact hfee h1
  have hfesurj : Function.Surjective fe := by
    intro u
    rcases zmod2_eq_one_or u _ hfee with h1 | h1
    · exact ⟨1, by rw [map_one, h1]⟩
    · exact ⟨_, h1.symm⟩
  have hN₁card : Nat.card N₁ * 2 = Nat.card C := by
    have h1 := fe.ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hfesurj, Subgroup.card_top,
      show Nat.card (Multiplicative (ZMod 2)) = 2 by simp] at h1
    rw [hN₁, Subgroup.card_map_of_injective C.subtype_injective, h1]
  have hSN₁odd : ¬ 2 ∣ S.relIndex N₁ := by
    have h1 := (S.subgroupOf N₁).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv, hScard] at h1
    have h2 := (T.subgroupOf C).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv, hT64] at h2
    have : S.relIndex N₁ = T.relIndex C := by
      change (S.subgroupOf N₁).index = (T.subgroupOf C).index
      omega
    rw [this]
    exact hodd
  obtain ⟨f₂, hf₂_odd, hf₂⟩ := exists_transfer_hom hSN hSN₁odd hK2'
  have hf₂v : f₂ ⟨v, hSN hvS⟩ ≠ 1 := by
    intro h1
    apply hvDT
    refine (hf₂ v hvS ?_).mp h1
    intro k a ha hconj
    have hvk : v ^ k = 1 ∨ v ^ k = v := by
      rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · left; rw [← two_mul, pow_mul, sq, hvv, one_pow]
      · right; rw [pow_succ, pow_mul, sq, hvv, one_pow, one_mul]
    rcases hvk with h2 | h2 <;> rw [h2] at hconj ⊢
    · simp only [mul_one, inv_mul_cancel, DT.one_mem]
    · refine iff_of_false (fun hD => ?_) hvDT
      obtain ⟨g, hgC, hg⟩ := hzDT _ hD (hvz.trans (isConj_iff.mpr ⟨a⁻¹, by group⟩))
      apply hvII (a * g) (C.mul_mem (hN₁C ha) hgC)
      calc a * g * z * (a * g)⁻¹ = a * (g * z * g⁻¹) * a⁻¹ := by group
        _ = v := by rw [hg]; group
  have hXN : X ≤ N₁ := fun x hx => (hfe_mem x (hXC hx)).mp (hfeX x hx)
  have hf₂X : ∀ x (hx : x ∈ X), f₂ ⟨x, hXN hx⟩ = 1 := fun x hx =>
    opResidual_le_ker hXN f₂ hf₂_odd hx
  have hf₂t : f₂ ⟨t, hSN htS⟩ = 1 := by
    refine (hf₂ t htS ?_).mpr htDT
    intro k a ha _
    rw [show a⁻¹ * t ^ k * a = t ^ k by
      rw [mul_assoc, (Commute.pow_left (show Commute t a from (hcen a (hN₁C ha)).symm) k).eq,
        inv_mul_cancel_left]]
  have hf₂DT : ∀ w (hw : w ∈ DT), f₂ ⟨w, hSN (hDTS hw)⟩ = 1 := by
    intro w hw
    rcases hw with hw | hw
    · exact hf₂X w (hDX hw)
    · have h1 : f₂ ⟨t * w, hSN (hDTS (Or.inl hw))⟩ = 1 := hf₂X _ (hDX hw)
      have e1 : (⟨t * w, hSN (hDTS (Or.inl hw))⟩ : ↥N₁) =
          ⟨t, hSN htS⟩ * ⟨w, hSN (hDTS (Or.inr hw))⟩ := rfl
      rw [e1, map_mul, hf₂t, one_mul] at h1
      exact h1
  have hRDT : ∀ x ∈ X ⊓ T, x ∈ DT := by
    rintro x ⟨hxX, hxT⟩
    have hxS : x ∈ S := hTN x hxT (hXN hxX)
    by_contra hxD
    have hxv : x * v ∈ DT := (hK2' _ hxS _ hvS).mpr (iff_of_false hxD hvDT)
    have h1 := hf₂DT _ hxv
    have e1 : (⟨x * v, hSN (hDTS hxv)⟩ : ↥N₁) = ⟨x, hXN hxX⟩ * ⟨v, hSN hvS⟩ := rfl
    rw [e1, map_mul, hf₂X x hxX, one_mul] at h1
    exact hf₂v h1
  have hTnorm : T ≤ Subgroup.normalizer (X : Set G) := le_normalizer_opResidual hTC
  have hXT : X ⊔ T = C := opResidual_sup_eq hTC hodd
  have hprod : Nat.card C * Nat.card ↥(X ⊓ T) = Nat.card X * Nat.card T := by
    have := card_sup_mul_card_inf_of_le_normalizer hTnorm
    rw [sup_comm, hXT, inf_comm] at this
    rw [this, mul_comm]
  have htX : t ∉ X := by
    intro htX
    have hRDT' : X ⊓ T = DT := by
      refine le_antisymm (fun x hx => hRDT x hx) ?_
      rintro w (hw | hw)
      · exact ⟨hDX hw, hST (hDS hw)⟩
      · have hw' : w = t * (t * w) := by rw [← mul_assoc, htt, one_mul]
        rw [hw']
        exact ⟨X.mul_mem htX (hDX hw), T.mul_mem (hST htS) (hST (hDS hw))⟩
    have hRp : IsPGroup 2 ↥(X ⊓ T) := by
      refine IsPGroup.of_card (n := 4) ?_
      rw [hRDT', hDTcard]; norm_num
    have hR16 : Nat.card ↥(X ⊓ T) = 16 := by rw [hRDT', hDTcard]
    have hRodd : ¬ 2 ∣ (X ⊓ T).relIndex X := by
      have h1 := ((X ⊓ T).subgroupOf X).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
      have h2 := (T.subgroupOf C).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv] at h2
      have : (X ⊓ T).relIndex X = T.relIndex C := by
        change ((X ⊓ T).subgroupOf X).index = (T.subgroupOf C).index
        rw [hR16] at h1 hprod
        rw [hT64] at h2 hprod
        nlinarith
      rw [this]; exact hodd
    have hDidx : D.relIndex (X ⊓ T) = 2 := by
      have h1 := (D.subgroupOf (X ⊓ T)).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (fun d hd => ⟨hDX hd, hST (hDS hd)⟩ : D ≤ X ⊓ T)).toEquiv, hDcard, hR16] at h1
      change (D.subgroupOf (X ⊓ T)).index = 2
      omega
    have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact htt) ht1
    have hnot := thompson_transfer_lemma_subgroup (inf_le_left : X ⊓ T ≤ X) hRp hRodd
      (fun d hd => ⟨hDX hd, hST (hDS hd)⟩) hDidx htX ht2 (by
        intro x hx hxD
        apply htD
        rwa [show x⁻¹ * t * x = t by
          rw [mul_assoc, ← hcen x (hXC hx), inv_mul_cancel_left]] at hxD)
    exact hnot (opResidual_le_pResidualOf X (opResidual_le_opResidual_self C htX))
  have hRD : X ⊓ T = D := by
    refine le_antisymm (fun x hx => ?_) (fun d hd => ⟨hDX hd, hST (hDS hd)⟩)
    rcases hRDT x hx with hxD | hxD
    · exact hxD
    · exfalso
      apply htX
      have : t = (t * x) * x⁻¹ := by group
      rw [this]
      exact X.mul_mem (hDX hxD) (X.inv_mem hx.1)
  refine ⟨hRD, ?_⟩
  rw [hRD, hDcard, hT64] at hprod
  omega

end HSSetting

end CFSG.Quasithin.HSType
