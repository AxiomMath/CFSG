module

public import CFSG.Quasithin.Recognition.HSType15e
public import CFSG.Quasithin.Recognition.L34AmalgamIso
public import CFSG.Quasithin.Recognition.HSType129g
public import CFSG.Quasithin.Recognition.HSType15c

public section

namespace CFSG.Quasithin.L34Amalgam.IsParabolic

theorem subgroupOf {L : Type*} [Group L] {K E Y : Subgroup L} {a b : L}
    (h : IsParabolic K E a b) (hK : K ≤ Y) :
    IsParabolic (K.subgroupOf Y) (E.subgroupOf Y) ⟨a, hK h.mem_a⟩ ⟨b, hK h.mem_b⟩ := by
  have hcl : (Subgroup.closure {(⟨a, hK h.mem_a⟩ : ↥Y), ⟨b, hK h.mem_b⟩}).map Y.subtype =
      Subgroup.closure {a, b} := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  refine ⟨fun x hx => Subgroup.mem_subgroupOf.mpr (h.le (Subgroup.mem_subgroupOf.mp hx)),
    fun x hx e he => Subgroup.mem_subgroupOf.mpr (h.normal _ (Subgroup.mem_subgroupOf.mp hx) _
      (Subgroup.mem_subgroupOf.mp he)),
    fun e he => Subtype.ext (h.mul_self _ (Subgroup.mem_subgroupOf.mp he)), ?_, ?_,
    Subgroup.mem_subgroupOf.mpr h.mem_a, Subgroup.mem_subgroupOf.mpr h.mem_b, ?_, ?_,
    Subtype.ext h.ha, Subtype.ext (by rw [Subgroup.coe_pow]; exact h.hb),
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_mul]; exact h.hab), ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le.trans hK)).toEquiv, h.card_E]
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv, h.card]
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun y ⟨hyE, hyC⟩ => Subtype.ext ?_
    have hy : (y : L) ∈ E ⊓ Subgroup.closure {a, b} :=
      ⟨Subgroup.mem_subgroupOf.mp hyE, hcl ▸ Subgroup.mem_map_of_mem _ hyC⟩
    rw [h.inf, Subgroup.mem_bot] at hy
    exact hy
  · rw [← Subgroup.card_map_of_injective Y.subtype_injective, hcl, h.card_C]
  · intro e he hc
    exact Subtype.ext (h.fpf _ (Subgroup.mem_subgroupOf.mp he) (congrArg Subtype.val hc))

end CFSG.Quasithin.L34Amalgam.IsParabolic

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.L34Amalgam MulAction
  CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

theorem pow_three_eq_one_of_sylow_E9 {G : Type*} [Group G] [Finite G] {C : Subgroup G} {m : ℕ}
    (hC : Nat.card C = 9 * m) (hm : ¬ 3 ∣ m) {x w p : G} (hx : x ∈ C) (hw : w ∈ C) (hp : p ∈ C)
    (hx3 : orderOf x = 3) (hw3 : orderOf w = 3) (hwx : w * x = x * w)
    (hwX : w ∉ Subgroup.zpowers x) (hp3 : p ^ 3 ∈ Subgroup.zpowers x) : p ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxxx : x ^ 3 = 1 := by rw [← hx3, pow_orderOf_eq_one]
  have hwww : w ^ 3 = 1 := by rw [← hw3, pow_orderOf_eq_one]
  set P₀ := Subgroup.zpowers x ⊔ Subgroup.zpowers w with hP₀
  have hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers w : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    have hc : ∀ k : ℤ, x * w ^ k * x⁻¹ = w ^ k := fun k => by
      rw [(Commute.zpow_right (show Commute x w from hwx.symm) k).eq, mul_inv_cancel_right]
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [hc]
      exact Subgroup.zpow_mem_zpowers w k
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      have : y = w ^ k := by
        calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
          _ = x⁻¹ * (x * w ^ k * x⁻¹) * x := by rw [← hk, hc]
          _ = w ^ k := by group
      rw [this]
      exact Subgroup.zpow_mem_zpowers w k
  have hcube : ∀ y ∈ P₀, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨k, q, hq, rfl⟩ := mem_sup_zpowers hxN hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    have hcomm : Commute (x ^ k) (w ^ j) :=
      Commute.zpow_zpow (show Commute x w from hwx.symm) k j
    have h1 : (x ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxxx, one_zpow]
    have h2 : (w ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hwww, one_zpow]
    rw [hcomm.mul_pow, h1, h2, one_mul]
  have hXW : Subgroup.zpowers x ⊓ Subgroup.zpowers w = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers w) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : Subgroup.zpowers x ⊓ Subgroup.zpowers w ≤ _)
      rwa [Nat.card_zpowers, hw3] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      apply hwX
      have hle : Subgroup.zpowers w ≤ Subgroup.zpowers x ⊓ Subgroup.zpowers w :=
        (Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, Nat.card_zpowers, hw3])).ge
      exact (hle (Subgroup.mem_zpowers w)).1
  have hcardP₀ : Nat.card P₀ = 9 := by
    have hXN : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers w : Set G) :=
      (Subgroup.zpowers_le).mpr hxN
    have := card_sup_mul_card_inf_of_le_normalizer hXN
    rw [hXW, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hx3, hw3] at this
    exact this
  have hP₀C : P₀ ≤ C := sup_le ((Subgroup.zpowers_le).mpr hx) ((Subgroup.zpowers_le).mpr hw)
  have hp9 : (p ^ 3) ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp3
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxxx, one_zpow]
  by_contra hp1
  have hop : orderOf p = 9 := by
    have hdvd : orderOf p ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one (by rw [← pow_mul] at hp9; exact hp9)
    rcases (Nat.dvd_prime_pow Nat.prime_three).mp hdvd with ⟨k, hk, hk'⟩
    interval_cases k
    · rw [pow_zero, orderOf_eq_one_iff] at hk'
      exact (hp1 (by rw [hk', one_pow])).elim
    · rw [pow_one] at hk'
      exact (hp1 (by rw [← hk', pow_orderOf_eq_one])).elim
    · rw [hk']
      norm_num
  obtain ⟨p', hp'⟩ : ∃ p' : ↥C, (p' : G) = p := ⟨⟨p, hp⟩, rfl⟩
  have hop' : orderOf p' = 9 := by rw [← Subgroup.orderOf_coe, hp', hop]
  have hp'p : IsPGroup 3 ↥(Subgroup.zpowers p') := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers, hop']; norm_num)
  have hP₀p : IsPGroup 3 ↥(P₀.subgroupOf C) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀C).toEquiv, hcardP₀]; norm_num)
  have hidx1 : ¬ 3 ∣ (Subgroup.zpowers p').index := by
    have h1 := (Subgroup.zpowers p').card_mul_index
    rw [Nat.card_zpowers, hop', hC] at h1
    have : (Subgroup.zpowers p').index = m := by omega
    rw [this]
    exact hm
  have hidx2 : ¬ 3 ∣ (P₀.subgroupOf C).index := by
    have h1 := (P₀.subgroupOf C).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀C).toEquiv, hcardP₀, hC] at h1
    have : (P₀.subgroupOf C).index = m := by omega
    rw [this]
    exact hm
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C (hp'p.toSylow hidx1) (hP₀p.toSylow hidx2)
  have hcp : c * p' * c⁻¹ ∈ P₀.subgroupOf C := by
    have h1 : c * p' * c⁻¹ ∈ (c • hp'p.toSylow hidx1 : Sylow 3 ↥C) := by
      rw [HSSetting.mem_smul_sylow', show c⁻¹ * (c * p' * c⁻¹) * c = p' by group]
      exact Subgroup.mem_zpowers _
    rw [hc] at h1
    exact h1
  have h3 := hcube _ (Subgroup.mem_subgroupOf.mp hcp)
  apply hp1
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hp', conj_pow] at h3
  calc p ^ 3 = (c : G)⁻¹ * ((c : G) * p ^ 3 * (c : G)⁻¹) * c := by group
    _ = 1 := by rw [h3]; group

namespace HSSetting

namespace S6Model

theorem exists_mulEquiv_L34
    {G : Type} [Group G] [Finite G] {z : G} {V : Subgroup G} {s : G} (M : S6Model z s)
    (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G}
    (hg₀ : g₀ * z * g₀⁻¹ = s) :
    ∃ g ∈ Subgroup.normalizer (M.V2 : Set G), g ∉ M.NN ∧
      ∃ Φ : ↥(M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom) ≃* stabilizer M22 (0 : Fin 22),
        (∀ x : ↥(M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom), (x : G) ∈ M.L1 ↔
          ((Φ x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab) ∧
        ∀ x : ↥(M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom),
          (x : G) ∈ M.L1.map (MulAut.conj g).toMonoidHom ↔
            ((Φ x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22PtHexStab := by
  classical
  obtain ⟨g, hg, hgNN⟩ := M.exists_g h hsmemH hsnotK hss hg₀
  obtain ⟨a, b, h₁, h₂, hE₁₂, hE₂₁, hne, hinf, hcard⟩ :=
    M.parabolics_of_g h hsmemH hsnotK hss hg₀ hg hgNN
  refine ⟨g, hg, hgNN, ?_⟩
  set L₂ := M.L1.map (MulAut.conj g).toMonoidHom with hL₂
  have hRXL₂ : M.RX ≤ L₂ := hinf ▸ inf_le_right
  obtain ⟨x, hx3, hπx, hxRX⟩ := M.exists_x2
  obtain ⟨j, -, hjx, gj, hgj⟩ := M.exists_j h hsmemH hsnotK hss hg₀ hx3 hπx
  obtain ⟨t, htt, htx, htl, htl0, ρ, -, hκ, hκ1, hfib⟩ :=
    M.exists_t1 h hsmemH hsnotK hss hg₀ hx3 hπx
  obtain ⟨n, hn⟩ := M.π_surj ρ
  have hπnt : M.π (n * t * n⁻¹) = ρ * M.π t * ρ⁻¹ := by rw [map_mul, map_mul, map_inv, hn]
  have hntt : ((n * t * n⁻¹ : ↥(hsNB z s)) : G) * ((n * t * n⁻¹ : ↥(hsNB z s)) : G) = 1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      show (n : G) * t * (n : G)⁻¹ * ((n : G) * t * (n : G)⁻¹) = n * ((t : G) * t) * (n : G)⁻¹ by
        group, htt, mul_one, mul_inv_cancel]
  obtain ⟨g₁, hg₁⟩ := M.conj_z_of_kleinS h hsmemH hsnotK hss hg₀ hg hgNN hntt
    (by rw [hπnt]; exact hκ) (by rw [hπnt]; exact hκ1) (by rw [hπnt]; exact hfib)
  have htz : ((n : G)⁻¹ * g₁) * z * ((n : G)⁻¹ * g₁)⁻¹ = t := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hg₁
    calc ((n : G)⁻¹ * g₁) * z * ((n : G)⁻¹ * g₁)⁻¹ = (n : G)⁻¹ * (g₁ * z * g₁⁻¹) * n := by group
      _ = t := by rw [hg₁]; group
  have htL₁ : (t : G) ∈ M.L1 := M.mem_pre.mpr ⟨t.2, htl⟩
  have htRX : (t : G) ∉ M.RX := fun hm => htl0 (M.π_mem_of_mem_pre hm t.2)
  have htL₂ : (t : G) ∉ L₂ := fun hm => htRX (by rw [← hinf]; exact ⟨htL₁, hm⟩)
  have hg' : g⁻¹ ∈ Subgroup.normalizer (M.V2 : Set G) := (Subgroup.normalizer _).inv_mem hg
  have hx₁RX : g⁻¹ * x * g ∈ M.RX := by
    have := M.conj_mem_RX h hsmemH hsnotK hss hg₀ hg' hxRX
    rwa [inv_inv] at this
  have hx₁3 : orderOf (g⁻¹ * x * g) = 3 := by
    rw [show g⁻¹ * (x : G) * g = MulAut.conj g⁻¹ x by simp, MulEquiv.orderOf_eq, hx3]
  obtain ⟨r, hrRX, hr⟩ := exists_conj_three_of_card (W := M.RX) (m := 64)
    (by rw [M.card_RX h hsmemH hsnotK hss hg₀]) (by decide) hxRX hx₁RX hx3 hx₁3
  have hrt : r * t * r⁻¹ * (g⁻¹ * x * g) * (r * t * r⁻¹)⁻¹ = (g⁻¹ * x * g)⁻¹ := by
    have htx' : (t : G) * (x : G)⁻¹ * (t : G)⁻¹ = x := by
      calc (t : G) * (x : G)⁻¹ * (t : G)⁻¹ = ((t : G) * x * (t : G)⁻¹)⁻¹ := by group
        _ = x := by rw [htx, inv_inv]
    rcases hr with hr | hr
    · rw [← hr]
      calc r * t * r⁻¹ * (r * x * r⁻¹) * (r * t * r⁻¹)⁻¹ = r * ((t : G) * x * (t : G)⁻¹) * r⁻¹ := by
            group
        _ = (r * x * r⁻¹)⁻¹ := by rw [htx]; group
    · have hr' : g⁻¹ * x * g = r * (x : G)⁻¹ * r⁻¹ := by
        rw [show r * (x : G)⁻¹ * r⁻¹ = (r * x * r⁻¹)⁻¹ by group, hr, inv_inv]
      rw [hr']
      calc r * t * r⁻¹ * (r * (x : G)⁻¹ * r⁻¹) * (r * t * r⁻¹)⁻¹ =
          r * ((t : G) * (x : G)⁻¹ * (t : G)⁻¹) * r⁻¹ := by group
        _ = (r * (x : G)⁻¹ * r⁻¹)⁻¹ := by rw [htx']; group
  set t₂ : G := g * (r * t * r⁻¹) * g⁻¹ with ht₂
  have ht₂2 : t₂ * t₂ = 1 := by
    rw [ht₂, show g * (r * t * r⁻¹) * g⁻¹ * (g * (r * t * r⁻¹) * g⁻¹) =
      g * r * ((t : G) * t) * r⁻¹ * g⁻¹ by group, htt]
    group
  have ht₂x : t₂ * x * t₂⁻¹ = (x : G)⁻¹ := by
    rw [ht₂]
    calc g * (r * t * r⁻¹) * g⁻¹ * x * (g * (r * t * r⁻¹) * g⁻¹)⁻¹ =
        g * (r * t * r⁻¹ * (g⁻¹ * x * g) * (r * t * r⁻¹)⁻¹) * g⁻¹ := by group
      _ = (x : G)⁻¹ := by rw [hrt]; group
  have hrtL₁ : r * t * r⁻¹ ∈ M.L1 :=
    M.L1.mul_mem (M.L1.mul_mem (M.RX_le_L1 hrRX) htL₁) (M.L1.inv_mem (M.RX_le_L1 hrRX))
  have ht₂L₂ : t₂ ∈ L₂ := by
    rw [hL₂, mem_map_conj_iff, ht₂, show g⁻¹ * (g * (r * t * r⁻¹) * g⁻¹) * g = r * t * r⁻¹ by
      group]
    exact hrtL₁
  have ht₂L₁ : t₂ ∉ M.L1 := by
    intro hm
    have hRX : t₂ ∈ M.RX := by rw [← hinf]; exact ⟨hm, ht₂L₂⟩
    have := M.conj_mem_RX h hsmemH hsnotK hss hg₀ hg' hRX
    rw [ht₂, inv_inv, show g⁻¹ * (g * (r * t * r⁻¹) * g⁻¹) * g = r * t * r⁻¹ by group] at this
    apply htRX
    have h2 := M.RX.mul_mem (M.RX.mul_mem (M.RX.inv_mem hrRX) this) hrRX
    rwa [show r⁻¹ * (r * t * r⁻¹) * r = (t : G) by group] at h2
  have ht₂z : (g * r * ((n : G)⁻¹ * g₁)) * z * (g * r * ((n : G)⁻¹ * g₁))⁻¹ = t₂ := by
    rw [ht₂]
    calc g * r * ((n : G)⁻¹ * g₁) * z * (g * r * ((n : G)⁻¹ * g₁))⁻¹ =
        g * r * (((n : G)⁻¹ * g₁) * z * ((n : G)⁻¹ * g₁)⁻¹) * r⁻¹ * g⁻¹ := by group
      _ = g * (r * t * r⁻¹) * g⁻¹ := by rw [htz]; group
  have h' : HSSetting j (V.map (MulAut.conj gj).toMonoidHom) := by
    have := h.conj gj
    rwa [hgj] at this
  have hxHj : (x : G) ∈ hsH j := Subgroup.mem_centralizer_singleton_iff.mpr hjx.symm
  have hjz : ∀ {y a : G}, a * z * a⁻¹ = y → (a * gj⁻¹) * j * (a * gj⁻¹)⁻¹ = y := by
    intro y a ha
    rw [← hgj, ← ha]
    group
  have hp : t * t₂ ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc (t : G) * t₂ * x = t * (t₂ * x * t₂⁻¹) * t₂ := by group
      _ = t * (x : G)⁻¹ * t₂ := by rw [ht₂x]
      _ = (t * (x : G)⁻¹ * (t : G)⁻¹) * (t * t₂) := by group
      _ = x * (t * t₂) := by
        rw [show (t : G) * (x : G)⁻¹ * (t : G)⁻¹ = ((t : G) * x * (t : G)⁻¹)⁻¹ by group, htx,
          inv_inv]
  have hmk : ((⟨t * t₂, hp⟩ : ↥(Subgroup.centralizer ({(x : G)} : Set G))) ^ 2 :
        ↥(Subgroup.centralizer ({(x : G)} : Set G))) ∈ cenX (x : G) ∨
      ((⟨t * t₂, hp⟩ : ↥(Subgroup.centralizer ({(x : G)} : Set G))) ^ 3 :
        ↥(Subgroup.centralizer ({(x : G)} : Set G))) ∈ cenX (x : G) ∧
      Nat.card ↥(Subgroup.centralizer ({(x : G)} : Set G)) =
        9 * (Nat.card (cenQuot (x : G)) / 3) ∧ ¬ 3 ∣ Nat.card (cenQuot (x : G)) / 3 := by
    have hcard : Nat.card ↥(Subgroup.centralizer ({(x : G)} : Set G)) =
        Nat.card (cenQuot (x : G)) * 3 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (cenX (x : G)),
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr rfl))).toEquiv, Nat.card_zpowers, hx3]
    rcases h'.cenQuot_s4_or_s5' hxHj hx3 with he | he
    · obtain ⟨e⟩ := he
      have hcQ : Nat.card (cenQuot (x : G)) = 24 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]; rfl
      rcases h'.mk_mul_pow_eq_one hxHj hx3 permFacts_four e htt ht₂2 htx ht₂x (hjz htz)
          (hjz ht₂z) hp with h2 | h3
      · left
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h2
        exact h2
      · right
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h3
        refine ⟨h3, ?_, ?_⟩
        · rw [hcard, hcQ]
        · rw [hcQ]; decide
    · obtain ⟨e⟩ := he
      have hcQ : Nat.card (cenQuot (x : G)) = 120 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]; rfl
      rcases h'.mk_mul_pow_eq_one hxHj hx3 permFacts_five e htt ht₂2 htx ht₂x (hjz htz)
          (hjz ht₂z) hp with h2 | h3
      · left
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h2
        exact h2
      · right
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h3
        refine ⟨h3, ?_, ?_⟩
        · rw [hcard, hcQ]
        · rw [hcQ]; decide
  have hxL₂ : (x : G) ∈ L₂ := hRXL₂ hxRX
  have hxL₁ : (x : G) ∈ M.L1 := M.RX_le_L1 hxRX
  obtain ⟨t₂', ht₂'2, ht₂'L₂, ht₂'L₁, ht₂'o⟩ : ∃ t₂' : G, t₂' * t₂' = 1 ∧ t₂' ∈ L₂ ∧
      t₂' ∉ M.L1 ∧ orderOf ((t : G) * t₂') ≤ 3 := by
    rcases hmk with h2 | ⟨h3, hcardC, hm⟩
    · rw [mem_cenX, Subgroup.coe_pow] at h2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
      have hkc : Commute ((t : G) * t₂) (x ^ k) :=
        Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hp) k
      refine ⟨t₂ * x ^ k, ?_, L₂.mul_mem ht₂L₂ (L₂.zpow_mem hxL₂ k), fun hm => ht₂L₁ ?_, ?_⟩
      · have : t₂ * x ^ k * t₂⁻¹ = (x : G) ^ (-k) := by
          rw [← conj_zpow, ht₂x, inv_zpow, zpow_neg]
        calc t₂ * x ^ k * (t₂ * x ^ k) = (t₂ * x ^ k * t₂⁻¹) * (t₂ * t₂) * x ^ k := by group
          _ = 1 := by rw [this, ht₂2, mul_one, ← zpow_add, neg_add_cancel, zpow_zero]
      · have := M.L1.mul_mem hm (M.L1.zpow_mem hxL₁ (-k))
        rwa [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one] at this
      · have hx3' : (x : G) ^ (3 : ℤ) = 1 := by
          rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hx3, pow_orderOf_eq_one]
        have hsq : ((t : G) * (t₂ * x ^ k)) ^ 2 = 1 := by
          rw [← mul_assoc, hkc.mul_pow, ← hk, ← zpow_natCast, ← zpow_mul, ← zpow_add,
            show k + k * ((2 : ℕ) : ℤ) = 3 * k by push_cast; ring, zpow_mul, hx3', one_zpow]
        exact (orderOf_le_of_pow_eq_one (by norm_num) hsq).trans (by norm_num)
    · rw [mem_cenX, Subgroup.coe_pow] at h3
      obtain ⟨w, hwx, hw3, hwX⟩ := h'.exists_mem_centralizer_three hxHj hx3
      have hp3 := pow_three_eq_one_of_sylow_E9 hcardC hm
        (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
        (Subgroup.mem_centralizer_singleton_iff.mpr hwx) hp hx3 hw3 hwx hwX h3
      exact ⟨t₂, ht₂2, ht₂L₂, ht₂L₁, orderOf_le_of_pow_eq_one (by norm_num) hp3⟩
  have hL1 : M.L1 ≤ M.L1 ⊔ L₂ := le_sup_left
  have hL2 : L₂ ≤ M.L1 ⊔ L₂ := le_sup_right
  have hgen : M.L1.subgroupOf (M.L1 ⊔ L₂) ⊔ L₂.subgroupOf (M.L1 ⊔ L₂) = ⊤ :=
    codisjoint_iff.mp (Subgroup.codisjoint_subgroupOf_sup M.L1 L₂)
  have hBL : hsB z s ≤ M.L1 ⊔ L₂ := h₁.le.trans hL1
  have hB'L : (hsB z s).map (MulAut.conj g).toMonoidHom ≤ M.L1 ⊔ L₂ := h₂.le.trans hL2
  have hinf' : Nat.card ↥(M.L1.subgroupOf (M.L1 ⊔ L₂) ⊓ L₂.subgroupOf (M.L1 ⊔ L₂)) = 192 := by
    have e : M.L1.subgroupOf (M.L1 ⊔ L₂) ⊓ L₂.subgroupOf (M.L1 ⊔ L₂) =
        (M.L1 ⊓ L₂).subgroupOf (M.L1 ⊔ L₂) := by
      ext y
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hL1)).toEquiv, hcard]
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ := exists_mulEquiv_m22Stab_of_parabolics hgen (h₁.subgroupOf hL1)
    (h₂.subgroupOf hL2)
    (fun y hy => Subgroup.mem_subgroupOf.mpr (hE₁₂ (Subgroup.mem_subgroupOf.mp hy)))
    (fun y hy => Subgroup.mem_subgroupOf.mpr (hE₂₁ (Subgroup.mem_subgroupOf.mp hy)))
    (fun he => hne (by
      have := Subgroup.subgroupOf_inj.mp he
      rwa [inf_eq_left.mpr hBL, inf_eq_left.mpr hB'L] at this))
    hinf' (t₁ := ⟨t, hL1 htL₁⟩) (t₂ := ⟨t₂', hL2 ht₂'L₂⟩)
    (Subgroup.mem_subgroupOf.mpr htL₁) (fun hm => htL₂ (Subgroup.mem_subgroupOf.mp hm))
    (Subgroup.mem_subgroupOf.mpr ht₂'L₂) (fun hm => ht₂'L₁ (Subgroup.mem_subgroupOf.mp hm))
    (Subtype.ext htt) (Subtype.ext ht₂'2) (by rw [← Subgroup.orderOf_coe]; exact ht₂'o)
  exact ⟨Φ, fun y => Subgroup.mem_subgroupOf.symm.trans (hΦ₁ y),
    fun y => Subgroup.mem_subgroupOf.symm.trans (hΦ₂ y)⟩

end S6Model

end HSSetting

end CFSG.Quasithin.HSType
