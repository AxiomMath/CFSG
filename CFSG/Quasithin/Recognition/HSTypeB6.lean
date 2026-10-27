module

public import CFSG.Quasithin.Recognition.HSTypeB5
public import CFSG.Quasithin.Recognition.HSTypeS6b

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

theorem not_fix_perp_of_fpf : ∀ σ : Equiv.Perm (Fin 6), (∀ x, σ x ≠ x) →
    ¬ ∀ v : SpV, spForm (spE 0) v = 0 → actS6 σ v = v := by
  decide +kernel

namespace HSSetting

variable {z : G} {V : Subgroup G} {s : G}

abbrev hsNB (z s : G) : Subgroup G := Subgroup.normalizer (hsB z s : Set G)

structure S6Model (z s : G) where
  Φ : SpV → G
  π : ↥(Subgroup.normalizer (hsB z s : Set G)) →* Equiv.Perm (Fin 6)
  mem : ∀ v, Φ v ∈ hsB z s
  inj : Function.Injective Φ
  add : ∀ v w, Φ (v + w) = Φ v * Φ w
  surj : ∀ x ∈ hsB z s, ∃ v, Φ v = x
  e0 : Φ (spE 0) = z
  e1 : Φ (spE 1) = s
  polar : ∀ u v, u ≠ 0 → (Φ v ∈ hsQ (Φ u) ↔ spForm u v = 0)
  π_surj : Function.Surjective π
  ker : ∀ n : ↥(Subgroup.normalizer (hsB z s : Set G)), π n = 1 ↔ (n : G) ∈ hsB z s
  act : ∀ (n : ↥(Subgroup.normalizer (hsB z s : Set G))) (v : SpV),
    (n : G) * Φ v * (n : G)⁻¹ = Φ (actS6 (π n) v)

theorem nonempty_s6Model [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) :
    Nonempty (S6Model z s) := by
  obtain ⟨Φ, π, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    h.exists_s6Model hsmemH hsnotK hss hg₀
  exact ⟨⟨Φ, π, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩⟩

namespace S6Model

variable (M : S6Model z s)

theorem Φ_zero : M.Φ 0 = 1 := by
  have := M.add 0 0
  rw [add_zero] at this
  exact mul_eq_left.mp this.symm

theorem mem_Q_iff (v : SpV) : M.Φ v ∈ hsQ z ↔ spForm (spE 0) v = 0 := by
  have := M.polar (spE 0) v (by decide)
  rwa [M.e0] at this

theorem comm_of_mul_invol {t b : G} (htt : t * t = 1) (hb : b * b = 1)
    (htb : t * b * (t * b) = 1) : t * b = b * t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have e : (t * b)⁻¹ = t * b := inv_eq_of_mul_eq_one_left htb
  rw [mul_inv_rev, htinv, hbinv] at e
  exact e.symm

theorem π_w [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {w : G} (hwZ : w ∈ hsZQ z) (hwz : w ∉ Subgroup.zpowers z)
    (hwN : w ∈ Subgroup.normalizer (hsB z s : Set G)) :
    M.π ⟨w, hwN⟩ = Equiv.swap 0 1 := by
  have hw1 : w ≠ 1 := fun h1 => hwz (h1 ▸ (Subgroup.zpowers z).one_mem)
  have hwz' : w ≠ z := fun h1 => hwz (h1 ▸ Subgroup.mem_zpowers z)
  have hww : w * w = z := by
    rcases h.z_eq_or_sq_of_mem_ZQ hwZ hw1 with h1 | h1
    · exact absurd h1.symm hwz'
    · exact h1.symm
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  have hsw : s * w * s⁻¹ = w⁻¹ := h.inv_of_not_mem_K hsmemH hsnotK hwZ
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left h.z_mul_z
  have hwsw : w * s * w⁻¹ = z * s := by
    have e1 : w * s = s * w⁻¹ := by
      calc w * s = s * (s⁻¹ * w * s) := by group
        _ = s * (s * w * s⁻¹) := by rw [hsinv]
        _ = s * w⁻¹ := by rw [hsw]
    calc w * s * w⁻¹ = s * (w * w)⁻¹ := by rw [e1]; group
      _ = s * z := by rw [hww, hzinv]
      _ = z * s := (Subgroup.mem_centralizer_singleton_iff.mp hsmemH)
  apply actS6_injective
  intro v
  apply M.inj
  rw [← M.act, actS6_swap01 v]
  show w * M.Φ v * w⁻¹ = M.Φ (v + spForm (spE 0) v • spE 0)
  rcases zmod2_cases (spForm (spE 0) v) with h0 | h1
  · rw [h0, zero_smul, add_zero]
    have hQ := (M.mem_Q_iff v).mpr h0
    rw [(Subgroup.mem_centralizer_iff.mp hwZ.2 _ hQ).symm, mul_inv_cancel_right]
  · rw [h1, one_smul, M.add, M.e0]
    have hQ : M.Φ v ∉ hsQ z := fun hQ => by
      rw [M.mem_Q_iff] at hQ
      rw [hQ] at h1
      exact absurd h1 (by decide)
    have hx := M.mem v
    rcases (mem_hsB_iff hss).mp hx with hx' | hx'
    · exact absurd hx'.1 hQ
    · have hwc : w * (s * M.Φ v) * w⁻¹ = s * M.Φ v := by
        rw [(Subgroup.mem_centralizer_iff.mp hwZ.2 _ hx'.1).symm, mul_inv_cancel_right]
      have hxz : M.Φ v * z = z * M.Φ v :=
        (Subgroup.mem_centralizer_singleton_iff.mp (h.hsB_le_H hsmemH hx))
      calc w * M.Φ v * w⁻¹ = (w * s * w⁻¹) * (w * (s * M.Φ v) * w⁻¹) := by
            conv_lhs => rw [show M.Φ v = s * (s * M.Φ v) by rw [← mul_assoc, hss, one_mul]]
            group
        _ = z * s * (s * M.Φ v) := by rw [hwsw, hwc]
        _ = z * M.Φ v := by rw [mul_assoc, ← mul_assoc s s, hss, one_mul]
        _ = M.Φ v * z := hxz.symm

theorem π_Q [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) {q : G} (hq : q ∈ hsQ z)
    (hqN : q ∈ Subgroup.normalizer (hsB z s : Set G)) :
    M.π ⟨q, hqN⟩ * M.π ⟨q, hqN⟩ = 1 ∧ ∀ v : SpV, spForm (spE 0) v = 0 →
      actS6 (M.π ⟨q, hqN⟩) v = v ∨ actS6 (M.π ⟨q, hqN⟩) v = v + spE 0 := by
  have hzC : z ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G) :=
    ⟨h.mem_Q, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hsmemH).symm⟩
  refine ⟨?_, fun v hv => ?_⟩
  · rw [← map_mul]
    refine (M.ker _).mpr ?_
    show q * q ∈ hsB z s
    rcases h.mul_self_eq_one_or_z hq with h1 | h1 <;> rw [h1]
    · exact (hsB z s).one_mem
    · exact h.z_mem_hsB hsmemH
  · have hvQ : M.Φ v ∈ hsQ z := (M.mem_Q_iff v).mpr hv
    have hact := M.act ⟨q, hqN⟩ v
    simp only at hact
    rcases h.comm_eq_one_or_z hq hvQ with h1 | h1
    · left
      apply M.inj
      rw [← hact]
      calc q * M.Φ v * q⁻¹ = q * M.Φ v * q⁻¹ * (M.Φ v)⁻¹ * M.Φ v := by group
        _ = M.Φ v := by rw [h1, one_mul]
    · right
      apply M.inj
      rw [← hact, M.add, M.e0]
      calc q * M.Φ v * q⁻¹ = q * M.Φ v * q⁻¹ * (M.Φ v)⁻¹ * M.Φ v := by group
        _ = z * M.Φ v := by rw [h1]
        _ = M.Φ v * z :=
          (Subgroup.mem_centralizer_singleton_iff.mp (h.hsB_le_H hsmemH (M.mem v))).symm

theorem conj_z_of_fpf [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1)
    {n : ↥(Subgroup.normalizer (hsB z s : Set G))} (hnn : (n : G) * n = 1)
    (hfpf : ∀ x, M.π n x ≠ x) : ∃ g : G, g * z * g⁻¹ = n := by
  obtain ⟨w, hwZ, hw1, hwz', -⟩ := h.exists_mem_ZQ_ne
  have hwz : w ∉ Subgroup.zpowers z := by
    intro hwz
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hwz with h1 | h1
    · exact hw1 h1
    · exact hwz' h1
  have hQN := h.Q_le_normalizer_hsB hsmemH hsnotK hss
  have hwN : w ∈ hsNB z s := hQN hwZ.1
  have hπw := M.π_w h hsmemH hsnotK hss hwZ hwz hwN
  set C := hsQ z ⊓ Subgroup.centralizer ({s} : Set G) with hC
  have hCZ := h.centralizer_invol_inf_ZQ hsmemH hsnotK
  have hZw := h.zpowers_eq_ZQ hwZ hwz
  have hcardCw : Nat.card ↥(C ⊔ hsZQ z) = 16 := by
    have hle : C ≤ Subgroup.normalizer (hsZQ z : Set G) :=
      (inf_le_left.trans h.Q_le_H).trans h.H_le_normalizer_ZQ
    have hprod := card_sup_mul_card_inf_of_le_normalizer hle
    rw [hCZ, Nat.card_zpowers, h.orderOf_z, h.card_ZQ,
      h.card_centralizer_invol hsmemH hsnotK hss] at hprod
    omega
  obtain ⟨q, hq, hqC⟩ : ∃ q ∈ hsQ z, q ∉ C ⊔ hsZQ z := by
    by_contra hne
    push Not at hne
    have := Subgroup.card_le_of_le (show hsQ z ≤ C ⊔ hsZQ z from hne)
    rw [h.card_Q, hcardCw] at this
    omega
  have hBQ : ∀ x ∈ hsQ z, x ∈ hsB z s → x ∈ C := fun x hx hxB =>
    (hsB_inf_Q hss (fun hsQ => hsnotK (h.Q_le_K hsQ))).le ⟨hxB, hx⟩
  have hqN := hQN hq
  have hπq1 : M.π ⟨q, hqN⟩ ≠ 1 := fun h1 =>
    hqC (Subgroup.mem_sup_left (hBQ q hq ((M.ker _).mp h1)))
  have hπqw : M.π ⟨q, hqN⟩ ≠ Equiv.swap 0 1 := by
    intro h1
    apply hqC
    have h2 : M.π (⟨w, hwN⟩⁻¹ * ⟨q, hqN⟩) = 1 := by rw [map_mul, map_inv, hπw, h1, inv_mul_cancel]
    have h3 := hBQ _ ((hsQ z).mul_mem ((hsQ z).inv_mem hwZ.1) hq) ((M.ker _).mp h2)
    have e : q = w * (w⁻¹ * q) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hwZ) (Subgroup.mem_sup_left h3)
  obtain ⟨q', hq', hq'N, hsign, hq'w⟩ : ∃ q' ∈ hsQ z, ∃ hq'N : q' ∈ hsNB z s,
      Equiv.Perm.sign (M.π ⟨q', hq'N⟩) = -1 ∧ M.π ⟨q', hq'N⟩ ≠ Equiv.swap 0 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (M.π ⟨q, hqN⟩)) with h1 | h1
    · refine ⟨q * w, (hsQ z).mul_mem hq hwZ.1, (hsNB z s).mul_mem hqN hwN, ?_, ?_⟩
      · have : M.π ⟨q * w, (hsNB z s).mul_mem hqN hwN⟩ = M.π ⟨q, hqN⟩ * Equiv.swap 0 1 := by
          rw [← hπw, ← map_mul]
          rfl
        rw [this, map_mul, h1, one_mul, Equiv.Perm.sign_swap (by decide)]
      · intro h2
        apply hπq1
        have : M.π ⟨q * w, (hsNB z s).mul_mem hqN hwN⟩ = M.π ⟨q, hqN⟩ * Equiv.swap 0 1 := by
          rw [← hπw, ← map_mul]
          rfl
        rw [this] at h2
        calc M.π ⟨q, hqN⟩ = M.π ⟨q, hqN⟩ * Equiv.swap 0 1 * Equiv.swap 0 1 := by
              rw [mul_assoc, Equiv.swap_mul_self, mul_one]
          _ = 1 := by rw [h2, Equiv.swap_mul_self]
    · exact ⟨q, hq, hqN, h1, hπqw⟩
  obtain ⟨hq'sq, hq'unip⟩ := M.π_Q h hsmemH hq' hq'N
  have hq'fpf := fpf_of_odd_of_unipotent _ hq'sq hsign hq'w hq'unip
  obtain ⟨i, hiQ, hiN, hii, hπi⟩ : ∃ i ∈ hsQ z, ∃ hiN : i ∈ hsNB z s, i * i = 1 ∧
      M.π ⟨i, hiN⟩ = M.π ⟨q', hq'N⟩ := by
    rcases h.mul_self_eq_one_or_z hq' with h1 | h1
    · exact ⟨q', hq', hq'N, h1, rfl⟩
    · obtain ⟨c, hcC, hcq⟩ : ∃ c ∈ C, q' * c ≠ c * q' := by
        by_contra hne
        push Not at hne
        apply not_fix_perp_of_fpf _ hq'fpf
        intro v hv
        apply M.inj
        rw [← M.act]
        show q' * M.Φ v * q'⁻¹ = M.Φ v
        have hvC : M.Φ v ∈ C := hBQ _ ((M.mem_Q_iff v).mpr hv) (M.mem v)
        rw [hne _ hvC, mul_inv_cancel_right]
      have hcomm : q' * c * q'⁻¹ * c⁻¹ = z := by
        rcases h.comm_eq_one_or_z hq' hcC.1 with h2 | h2
        · exfalso
          apply hcq
          calc q' * c = q' * c * q'⁻¹ * c⁻¹ * (c * q') := by group
            _ = c * q' := by rw [h2, one_mul]
        · exact h2
      have hcc : c * c = 1 := h.mul_self_of_mem_centralizer_invol hsmemH hsnotK hss hcC
      have hcB : c ∈ hsB z s := centralizer_le_hsB hcC
      refine ⟨q' * c, (hsQ z).mul_mem hq' hcC.1, (hsNB z s).mul_mem hq'N (hQN hcC.1), ?_, ?_⟩
      · have hzc : z * c = c * z := (h.comm_z_of_mem_Q hcC.1).symm
        have e : q' * c = z * c * q' := by rw [← hcomm]; group
        calc q' * c * (q' * c) = z * c * q' * (q' * c) := by rw [e]
          _ = z * c * (q' * q') * c := by group
          _ = z * c * z * c := by rw [h1]
          _ = (z * z) * (c * c) := by
            rw [show z * c * z * c = z * (c * z) * c by group, ← hzc]; group
          _ = 1 := by rw [h.z_mul_z, hcc, one_mul]
      · have : M.π ⟨c, hQN hcC.1⟩ = 1 := (M.ker _).mpr hcB
        rw [show (⟨q' * c, (hsNB z s).mul_mem hq'N (hQN hcC.1)⟩ : ↥(hsNB z s)) =
          ⟨q', hq'N⟩ * ⟨c, hQN hcC.1⟩ from rfl, map_mul, this, mul_one]
  have hifpf : ∀ x, M.π ⟨i, hiN⟩ x ≠ x := by rw [hπi]; exact hq'fpf
  have hiZ : i ∉ hsZQ z := by
    intro hiZ
    apply not_fix_perp_of_fpf _ hifpf
    intro v hv
    apply M.inj
    rw [← M.act]
    show i * M.Φ v * i⁻¹ = M.Φ v
    rw [← Subgroup.mem_centralizer_iff.mp hiZ.2 _ ((M.mem_Q_iff v).mpr hv), mul_inv_cancel_right]
  obtain ⟨g₁, hg₁⟩ := h.exists_conj_z_of_invol_Q hiQ hii hiZ
  have hn2 : M.π n * M.π n = 1 := by
    rw [← map_mul]
    exact (M.ker _).mpr (by show (n : G) * n ∈ hsB z s; rw [hnn]; exact (hsB z s).one_mem)
  have hi2 : M.π ⟨i, hiN⟩ * M.π ⟨i, hiN⟩ = 1 := by
    rw [← map_mul]
    exact (M.ker _).mpr (by show i * i ∈ hsB z s; rw [hii]; exact (hsB z s).one_mem)
  obtain ⟨ρ1, hρ1⟩ := exists_conj_fpf _ hn2 hfpf
  obtain ⟨ρ2, hρ2⟩ := exists_conj_fpf _ hi2 hifpf
  obtain ⟨m, hm⟩ := M.π_surj (ρ2⁻¹ * ρ1)
  have hπn' : M.π (m * n * m⁻¹) = M.π ⟨i, hiN⟩ := by
    rw [map_mul, map_mul, map_inv, hm]
    calc ρ2⁻¹ * ρ1 * M.π n * (ρ2⁻¹ * ρ1)⁻¹ = ρ2⁻¹ * (ρ1 * M.π n * ρ1⁻¹) * ρ2 := by group
      _ = ρ2⁻¹ * (ρ2 * M.π ⟨i, hiN⟩ * ρ2⁻¹) * ρ2 := by rw [hρ1, hρ2]
      _ = M.π ⟨i, hiN⟩ := by group
  have hcB : (((⟨i, hiN⟩ : ↥(hsNB z s))⁻¹ * (m * n * m⁻¹) : ↥(hsNB z s)) : G) ∈ hsB z s :=
    (M.ker _).mp (by rw [map_mul, map_inv, hπn', inv_mul_cancel])
  set c : G := (((⟨i, hiN⟩ : ↥(hsNB z s))⁻¹ * (m * n * m⁻¹) : ↥(hsNB z s)) : G) with hc
  have hmn : (m : G) * n * (m : G)⁻¹ = i * c := by
    rw [hc]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hcc : c * c = 1 := h.hsB_sq hsmemH hsnotK hss hcB
  have hic : i * c = c * i := comm_of_mul_invol hii hcc (by
    rw [← hmn]
    calc (m : G) * n * (m : G)⁻¹ * ((m : G) * n * (m : G)⁻¹) = m * ((n : G) * n) * (m : G)⁻¹ := by
          group
      _ = 1 := by rw [hnn, mul_one, mul_inv_cancel])
  obtain ⟨v, hv⟩ := M.surj c hcB
  rw [← hv] at hic hmn
  have hfix : actS6 (M.π ⟨i, hiN⟩) v = v := by
    apply M.inj
    rw [← M.act]
    show i * M.Φ v * i⁻¹ = M.Φ v
    rw [hic, mul_inv_cancel_right]
  have hfix0 : actS6 fpf0 (actS6 ρ2 v) = actS6 ρ2 v := by
    rw [← actS6_mul, ← hρ2, show ρ2 * M.π ⟨i, hiN⟩ * ρ2⁻¹ * ρ2 = ρ2 * M.π ⟨i, hiN⟩ by group,
      actS6_mul, hfix]
  obtain ⟨u1, hu1⟩ := centralizer_fpf_eq_comm _ hfix0
  set u := actS6 ρ2⁻¹ u1 with hu
  have hvu : v = actS6 (M.π ⟨i, hiN⟩) u + u := by
    have e1 : v = actS6 ρ2⁻¹ (actS6 ρ2 v) := by rw [← actS6_mul, inv_mul_cancel, actS6_one]
    rw [e1, hu1, actS6_add, hu, ← actS6_mul, ← actS6_mul]
    congr 2
    calc ρ2⁻¹ * fpf0 = ρ2⁻¹ * (ρ2 * M.π ⟨i, hiN⟩ * ρ2⁻¹) := by rw [hρ2]
      _ = M.π ⟨i, hiN⟩ * ρ2⁻¹ := by group
  set x := M.Φ u with hx
  have hxx : x * x = 1 := h.hsB_sq hsmemH hsnotK hss (M.mem u)
  have hiinv : i⁻¹ = i := inv_eq_of_mul_eq_one_left hii
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hxx
  have hΦv : M.Φ v = i * x * i⁻¹ * x := by
    rw [hvu, M.add, ← M.act ⟨i, hiN⟩ u]
  refine ⟨(m : G)⁻¹ * x * g₁, ?_⟩
  have e2 : (m : G) * n * (m : G)⁻¹ = x * i * x⁻¹ := by
    rw [hmn, hΦv, hiinv, hxinv]
    calc i * (i * x * i * x) = (i * i) * x * i * x := by group
      _ = x * i * x := by rw [hii, one_mul]
  calc (m : G)⁻¹ * x * g₁ * z * ((m : G)⁻¹ * x * g₁)⁻¹ =
      (m : G)⁻¹ * x * (g₁ * z * g₁⁻¹) * x⁻¹ * m := by group
    _ = (m : G)⁻¹ * (x * i * x⁻¹) * m := by rw [hg₁]; group
    _ = n := by rw [← e2]; group

end S6Model

end HSSetting

end CFSG.Quasithin.HSType
