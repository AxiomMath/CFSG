module

public import CFSG.Quasithin.Recognition.HSTypeL12c
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4
open scoped MatrixGroups

variable {G : Type*} [Group G]

theorem perm_five_alt_order_four : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 →
    σ * σ * (σ * σ) = 1 → σ * σ = 1 := by
  decide +kernel

@[expose] def sl32a0 : SL(3, ZMod 2) := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

theorem sl32_invol_conj : ∀ b : SL(3, ZMod 2), b * b = 1 → b ≠ 1 →
    ∃ g : SL(3, ZMod 2), g * sl32a0 * g⁻¹ = b := by
  decide +kernel

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem P_le_K [Finite G] (h : HSSetting z V) : hsP V ≤ hsK z := fun _ hx =>
  ⟨h.P_le_H hx, Subgroup.mem_centralizer_iff.mpr fun _ hu =>
    h.P_comm (h.ZQ_le_P hu) hx⟩

theorem card_K [Finite G] (h : HSSetting z V) : Nat.card (hsK z) = 64 * 60 := by
  have h1 := Subgroup.card_mul_index ((hsK z).subgroupOf (hsH z))
  rw [h.index_K, h.card_H] at h1
  have h2 : Nat.card ((hsK z).subgroupOf (hsH z)) = Nat.card (hsK z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : hsK z ≤ hsH z)).toEquiv
  omega

theorem map_K_eq_alternating [Finite G] (h : HSSetting z V) (φ : ↥(hsH z) →* Equiv.Perm (Fin 5))
    (hker : φ.ker = (hsQ z).subgroupOf (hsH z)) :
    ((hsK z).subgroupOf (hsH z)).map φ = alternatingGroup (Fin 5) := by
  set B := ((hsK z).subgroupOf (hsH z)).map φ with hB
  set A := alternatingGroup (Fin 5) with hA
  have hBcard : Nat.card B = 60 := by
    have hQK : φ.ker ≤ (hsK z).subgroupOf (hsH z) := by
      rw [hker]
      intro x hx
      exact h.Q_le_K hx
    have hrange : (φ.comp ((hsK z).subgroupOf (hsH z)).subtype).range = B := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hkerc : (φ.comp ((hsK z).subgroupOf (hsH z)).subtype).ker =
        (φ.ker).subgroupOf ((hsK z).subgroupOf (hsH z)) := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    have hcK : Nat.card ((hsK z).subgroupOf (hsH z)) = 64 * 60 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : hsK z ≤ hsH z)).toEquiv,
        h.card_K]
    have hcQ : Nat.card ((φ.ker).subgroupOf ((hsK z).subgroupOf (hsH z))) = 64 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv, hker,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Q_le_H).toEquiv, h.card_Q]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (φ.comp ((hsK z).subgroupOf (hsH z)).subtype).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, hrange, hkerc, hcK,
      hcQ] at h1
    omega
  have hAcard : Nat.card A = 60 := by
    rw [hA, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hBidx : B.index = 2 := by
    have h1 := Subgroup.card_mul_index B
    rw [hBcard, Nat.card_perm, Nat.card_fin] at h1
    have : (5 : ℕ).factorial = 120 := rfl
    omega
  have hBn : B.Normal := Subgroup.normal_of_index_eq_two hBidx
  have hprod := card_sup_mul_card_inf_of_le_normalizer (X := A) (N := B)
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hBn]; exact le_top)
  have hsup : Nat.card ↥(A ⊔ B) ≤ 120 := by
    have := Subgroup.card_le_card_group (A ⊔ B)
    rwa [Nat.card_perm, Nat.card_fin] at this
  rw [hAcard, hBcard] at hprod
  have hinf : 30 ≤ Nat.card ↥(A ⊓ B) := by nlinarith
  have hdvd : Nat.card ↥(A ⊓ B) ∣ 60 := hAcard ▸ Subgroup.card_dvd_of_le inf_le_left
  have hle : Nat.card ↥(A ⊓ B) ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have h60 : Nat.card ↥(A ⊓ B) = 60 := by
    by_contra hne
    have h30 : Nat.card ↥(A ⊓ B) = 30 := by
      obtain ⟨c, hc⟩ := hdvd
      rcases c with _ | _ | c
      · omega
      · omega
      · nlinarith
    have : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
    have hidx : ((A ⊓ B).subgroupOf A).index = 2 := by
      have h1 := Subgroup.card_mul_index ((A ⊓ B).subgroupOf A)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, h30, hAcard] at h1
      omega
    have hn := Subgroup.normal_of_index_eq_two hidx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A ⊓ B).subgroupOf A) with hb | ht
    · rw [hb, Subgroup.index_bot, hAcard] at hidx
      omega
    · rw [ht, Subgroup.index_top] at hidx
      omega
  have hAB : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h60, hAcard])
  have hAle : A ≤ B := by
    rw [← hAB]
    exact inf_le_right
  exact (Subgroup.eq_of_le_of_card_ge hAle (by rw [hBcard, hAcard])).symm

theorem sq_mem_Q_of_mem_K [Finite G] (h : HSSetting z V) {k : G} (hk : k ∈ hsK z)
    (hk4 : k * k * (k * k) = 1) : k * k ∈ hsQ z := by
  obtain ⟨φ, -, hker⟩ := h.one.quot
  have hkerQ : ∀ g : ↥(hsH z), φ g = 1 ↔ (g : G) ∈ hsQ z := by
    intro g
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  set k' : ↥(hsH z) := ⟨k, hk.1⟩
  have hk'A : φ k' ∈ alternatingGroup (Fin 5) := by
    rw [← h.map_K_eq_alternating φ hker]
    exact ⟨k', hk, rfl⟩
  have hk'4 : φ k' * φ k' * (φ k' * φ k') = 1 := by
    rw [← map_mul, ← map_mul]
    have : k' * k' * (k' * k') = 1 := Subtype.ext hk4
    rw [this, map_one]
  have h2 := perm_five_alt_order_four (φ k') (Equiv.Perm.mem_alternatingGroup.mp hk'A) hk'4
  rw [← map_mul] at h2
  exact (hkerQ (k' * k')).mp h2

theorem mem_Q_of_conj_mem_K [Finite G] (h : HSSetting z V) {g : G}
    (hx : g * z * g⁻¹ ∈ hsK z) : g * z * g⁻¹ ∈ hsQ z := by
  obtain ⟨u, huZ, -, -, huu⟩ := h.exists_mem_ZQ_ne
  have hconjH : ∀ a ∈ hsZQ z, g⁻¹ * a * g ∈ hsH z := by
    intro a ha
    have hax : a * (g * z * g⁻¹) = (g * z * g⁻¹) * a :=
      Subgroup.mem_centralizer_iff.mp hx.2 a ha
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc g⁻¹ * a * g * z = g⁻¹ * (a * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * a) * g := by rw [hax]
      _ = z * (g⁻¹ * a * g) := by group
  have hsqK : g⁻¹ * z * g ∈ hsK z := by
    have h2 := Subgroup.sq_mem_of_index_two h.index_K ⟨g⁻¹ * u * g, hconjH u huZ⟩
    rw [Subgroup.mem_subgroupOf, sq] at h2
    have : ((⟨g⁻¹ * u * g, hconjH u huZ⟩ * ⟨g⁻¹ * u * g, hconjH u huZ⟩ : ↥(hsH z)) : G) =
        g⁻¹ * z * g := by
      simp only [Subgroup.coe_mul]
      rw [← huu]
      group
    rwa [this] at h2
  have hconjH' : ∀ c ∈ hsZQ z, g * c * g⁻¹ ∈ hsH z := by
    intro c hc
    have hcz : c * (g⁻¹ * z * g) = (g⁻¹ * z * g) * c :=
      Subgroup.mem_centralizer_iff.mp hsqK.2 c hc
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc g * c * g⁻¹ * z = g * (c * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * c) * g⁻¹ := by rw [hcz]
      _ = z * (g * c * g⁻¹) := by group
  have hcomm : ∀ a ∈ hsZQ z, ∀ c ∈ hsZQ z,
      a * (g * c * g⁻¹) * a⁻¹ * (g * c * g⁻¹)⁻¹ ∈ hsZQ z ⊓ CFSG.conjugate (hsZQ z) g⁻¹ := by
    intro a ha c hc
    refine ⟨?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_ZQ (hconjH' c hc)) a⁻¹).mp
        ((hsZQ z).inv_mem ha)
      have : a * (g * c * g⁻¹) * a⁻¹ * (g * c * g⁻¹)⁻¹ =
          a * ((g * c * g⁻¹) * a⁻¹ * (g * c * g⁻¹)⁻¹) := by group
      rw [this]
      exact (hsZQ z).mul_mem ha h1
    · show a * (g * c * g⁻¹) * a⁻¹ * (g * c * g⁻¹)⁻¹ ∈ CFSG.conjugate (hsZQ z) g⁻¹
      rw [mem_conjugate_iff', inv_inv]
      have h1 := (Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_ZQ (hconjH a ha)) c).mp hc
      have : g⁻¹ * (a * (g * c * g⁻¹) * a⁻¹ * (g * c * g⁻¹)⁻¹) * g =
          (g⁻¹ * a * g) * c * (g⁻¹ * a * g)⁻¹ * c⁻¹ := by group
      rw [this]
      exact (hsZQ z).mul_mem h1 ((hsZQ z).inv_mem hc)
  by_cases hmeet : hsZQ z ⊓ CFSG.conjugate (hsZQ z) g⁻¹ = ⊥
  ·
    have hguK : g * u * g⁻¹ ∈ hsK z := by
      refine ⟨hconjH' u huZ, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      have h1 := hcomm a ha u huZ
      rw [hmeet, Subgroup.mem_bot] at h1
      have : a * (g * u * g⁻¹) = (g * u * g⁻¹) * a := by
        rw [mul_inv_eq_one] at h1
        calc a * (g * u * g⁻¹) = a * (g * u * g⁻¹) * a⁻¹ * a := by group
          _ = g * u * g⁻¹ * a := by rw [h1]
      exact this
    have hgu4 : g * u * g⁻¹ * (g * u * g⁻¹) * (g * u * g⁻¹ * (g * u * g⁻¹)) = 1 := by
      have hzz : z * z = 1 := by rw [← sq]; exact h.sq_z
      calc g * u * g⁻¹ * (g * u * g⁻¹) * (g * u * g⁻¹ * (g * u * g⁻¹))
          = g * ((u * u) * (u * u)) * g⁻¹ := by group
        _ = 1 := by rw [huu, hzz, mul_one, mul_inv_cancel]
    have := h.sq_mem_Q_of_mem_K hguK hgu4
    have heq : g * u * g⁻¹ * (g * u * g⁻¹) = g * z * g⁻¹ := by rw [← huu]; group
    rwa [heq] at this
  ·
    have hEq := h.conjugate_ZQ_eq_of_ne_bot hmeet
    have hgzZ : g * z * g⁻¹ ∈ hsZQ z := by
      rw [← hEq, mem_conjugate_iff', inv_inv]
      have : g⁻¹ * (g * z * g⁻¹) * g = z := by group
      rw [this]
      exact h.z_mem_ZQ
    exact hgzZ.1

theorem exists_isSylowTwoOf [Finite G] (_h : HSSetting z V) :
    ∃ T : Subgroup G, IsSylowTwoOf T (hsH z ⊓ hsM V) := by
  obtain ⟨T, hT, -⟩ := exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup G) ≤ hsH z ⊓ hsM V)
    IsPGroup.of_bot
  exact ⟨T, hT⟩

theorem exists_conj_mem_T [Finite G] (h : HSSetting z V) {T : Subgroup G}
    (hT : IsSylowTwoOf T (hsH z ⊓ hsM V)) {i : G} (hi : i * i = 1) :
    ∃ g : G, g * i * g⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo (h.isSylowTwo_T hT)
  have hip : IsPGroup 2 (Subgroup.zpowers i) := by
    refine IsPGroup.of_card (n := (orderOf i).log2) ?_
    rw [Nat.card_zpowers]
    have hdvd : orderOf i ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hi)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1 <;> rw [h1] <;> rfl
  obtain ⟨S', hS'⟩ := hip.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  refine ⟨g, ?_⟩
  rw [← hS, ← hg, Sylow.coe_subgroup_smul]
  exact ⟨i, hS' (Subgroup.mem_zpowers i), by simp [MulAut.smul_def]⟩

theorem exists_conj_mem_H_not_mem_K [Finite G] (h : HSSetting z V) {i : G} (hi : i * i = 1)
    (hi1 : i ≠ 1) : ∃ g : G, g * i * g⁻¹ ∈ hsH z ∧ g * i * g⁻¹ ∉ hsK z := by
  obtain ⟨s, ⟨hsHmem, hsMmem⟩, hss, hsinv, g₁, hg₁⟩ := h.exists_invol_inverts_ZQ
  obtain ⟨w, hwZ, -, -, hww⟩ := h.exists_mem_ZQ_ne
  have hsnotK : s ∉ hsK z := by
    intro hs
    have h1 := hsinv w hwZ
    rw [(Subgroup.mem_centralizer_iff.mp hs.2 w hwZ).symm, mul_inv_cancel_right] at h1
    have : w * w = 1 := by
      calc w * w = w * w⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel w
    rw [hww] at this
    exact h.z_ne_one this
  obtain ⟨T, hT⟩ := h.exists_isSylowTwoOf
  obtain ⟨g, hgT⟩ := h.exists_conj_mem_T hT hi
  set i' := g * i * g⁻¹ with hi'
  have hi'2 : i' * i' = 1 := by
    rw [hi']
    calc g * i * g⁻¹ * (g * i * g⁻¹) = g * (i * i) * g⁻¹ := by group
      _ = 1 := by rw [hi, mul_one, mul_inv_cancel]
  have hi'1 : i' ≠ 1 := by
    intro h1
    apply hi1
    calc i = g⁻¹ * i' * g := by rw [hi']; group
      _ = 1 := by rw [h1]; group
  have hi'M : i' ∈ hsM V := (hT.1.trans inf_le_right) hgT
  by_cases hi'P : i' ∈ hsP V
  ·
    have hi'V := h.mem_V_of_mem_P hi'P hi'2
    obtain ⟨m, -, hm⟩ := h.exists_conj_eq_of_mem_V hi'V hi'1
    have hconj : g₁ * m⁻¹ * g * i * (g₁ * m⁻¹ * g)⁻¹ = s := by
      calc g₁ * m⁻¹ * g * i * (g₁ * m⁻¹ * g)⁻¹ = g₁ * m⁻¹ * i' * m * g₁⁻¹ := by
            rw [hi']; group
        _ = g₁ * z * g₁⁻¹ := by rw [← hm]; group
        _ = s := hg₁
    refine ⟨g₁ * m⁻¹ * g, ?_, ?_⟩
    · rw [hconj]
      exact hsHmem
    · rw [hconj]
      exact hsnotK
  ·
    obtain ⟨θ, hθ, hker⟩ := h.two.quot
    have hkerP : ∀ x : ↥(hsM V), θ x = 1 ↔ (x : G) ∈ hsP V := by
      intro x
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    set a : ↥(hsM V) := ⟨i', hi'M⟩
    set b : ↥(hsM V) := ⟨s, hsMmem⟩
    have ha2 : θ a * θ a = 1 := by
      rw [← map_mul]
      have : a * a = 1 := Subtype.ext hi'2
      rw [this, map_one]
    have hb2 : θ b * θ b = 1 := by
      rw [← map_mul]
      have : b * b = 1 := Subtype.ext hss
      rw [this, map_one]
    have ha1 : θ a ≠ 1 := fun h1 => hi'P ((hkerP a).mp h1)
    have hb1 : θ b ≠ 1 := fun h1 => hsnotK (h.P_le_K ((hkerP b).mp h1))
    obtain ⟨ca, hca⟩ := sl32_invol_conj (θ a) ha2 ha1
    obtain ⟨cb, hcb⟩ := sl32_invol_conj (θ b) hb2 hb1
    obtain ⟨m, hm⟩ := hθ (cb * ca⁻¹)
    have hconj : θ (m * a * m⁻¹ * b⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hm, ← hca, ← hcb]
      group
    have hP : (m : G) * i' * (m : G)⁻¹ * s⁻¹ ∈ hsP V := (hkerP _).mp hconj
    have hmem : (m : G) * i' * (m : G)⁻¹ = ((m : G) * i' * (m : G)⁻¹ * s⁻¹) * s := by group
    refine ⟨m * g, ?_, ?_⟩
    · have : (m : G) * g * i * ((m : G) * g)⁻¹ = (m : G) * i' * (m : G)⁻¹ := by
        rw [hi']; group
      rw [this, hmem]
      exact (hsH z).mul_mem (h.P_le_H hP) hsHmem
    · have : (m : G) * g * i * ((m : G) * g)⁻¹ = (m : G) * i' * (m : G)⁻¹ := by
        rw [hi']; group
      rw [this, hmem]
      intro hK
      apply hsnotK
      have := (hsK z).mul_mem ((hsK z).inv_mem (h.P_le_K hP)) hK
      have heq : ((m : G) * i' * (m : G)⁻¹ * s⁻¹)⁻¹ * (((m : G) * i' * (m : G)⁻¹ * s⁻¹) * s) =
          s := by group
      rwa [heq] at this

end HSSetting

end CFSG.Quasithin.HSType
