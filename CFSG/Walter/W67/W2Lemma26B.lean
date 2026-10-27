module

public import CFSG.Walter.W67.W2Lemma26A

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_inf_normalizer_le (A B : Subgroup G) :
    Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rintro x ⟨hA, hB⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp hA,
    ← Subgroup.mem_normalizer_iff.mp hB]

namespace Frame

variable {h : Hyp G} (fr : Frame h)

theorem EX_le_E (X : Subgroup G) : fr.EX X ≤ fr.E := inf_le_left

theorem EX_le_normalizer (X : Subgroup G) : fr.EX X ≤ Subgroup.normalizer (X : Set G) :=
  inf_le_right

theorem EX_le_normalizer_KX (X : Subgroup G) :
    fr.EX X ≤ Subgroup.normalizer (h.KX X : Set G) := fun _ he =>
  normalizer_inf_normalizer_le h.K _
    ⟨h.H_le_normalizer (fr.E_le_H (fr.EX_le_E X he)),
      normalizer_le_normalizer_centralizer X (fr.EX_le_normalizer X he)⟩

theorem zpowers_J_le_normalizer (X : Subgroup G) :
    Subgroup.zpowers h.J ≤ Subgroup.normalizer ((h.KX X ⊔ fr.EX X : Subgroup G) : Set G) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro w hw
  have hwH : w ∈ h.H := (sup_le (inf_le_left.trans h.K_le_H)
    ((fr.EX_le_E X).trans fr.E_le_H)) hw
  exact h.commute_J hwH

end Frame

theorem MinCE.lspec_of_lt
    (m : MinCE G) (fr : Frame m.toHyp) (hJ : JFacts) (hR : RFacts)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) {X : Subgroup G} (hXE : X ≤ fr.E)
    (hX : X ≠ ⊥) (hr : 3 < m.p ^ (m.f / m.eX X)) (hne : Subgroup.centralizer (X : Set G) ≠ ⊤) :
    ∃ L : Subgroup G, LSpec m.toHyp fr X L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨eKX⟩, h21⟩ := lemma_2_6_i G m.toHyp fr hXE hX
  have hfe := fr.div_eX_pos hXE
  set NX := Subgroup.normalizer (X : Set G)
  set CX := Subgroup.centralizer (X : Set G)
  have hCN : CX ≤ NX := Subgroup.centralizer_le_normalizer _
  have hSC : (fr.S : Subgroup G) ≤ CX := fr.S_le_centralizer hXE
  have hKXC : m.KX X ≤ CX := inf_le_right
  have hKXH : m.KX X ≤ Subgroup.centralizer ({m.J} : Set G) := inf_le_left.trans m.K_le_H
  have hKn : ∀ x ∈ CX, x * m.J = m.J * x → ∀ k ∈ m.KX X, x * k * x⁻¹ ∈ m.KX X :=
    fun x hx hxJ k hk => ⟨m.conj_mem_K (m.mem_H_iff.mpr hxJ) hk.1,
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer X (hCN hx)) k).mp
        hk.2⟩
  have hcovC := fr.cover_le_centralizer hXE
  let hC : Hyp CX := m.ofSubgroup ⟨fr.S, hSC⟩ (hSC fr.J_mem) m.orderOf_J hKXC hKXH hKn m.p
    (m.f / m.eX X) m.p_ne_two hfe eKX
  have hidxC := fr.index_ne_two_X hidx hXE eKX hKXC (hcovC.trans Subgroup.le_normalizer)
  rcases m.ih CX hC (card_lt_of_ne_top hne) with hc | hc
  · obtain ⟨N, hN, h2⟩ := hC.exists_normal_index_two_of_case1 hc
    exact absurd h2 (index_ne_two_subtype hidxC N hN)
  obtain ⟨L, hLC, hLn, hLodd, -, ⟨K'', hK''L, hJK'', hCL, ⟨eK''⟩⟩, -⟩ :=
    m.case2_ofSubgroup ⟨fr.S, hSC⟩ (hSC fr.J_mem) m.orderOf_J hKXC hKXH hKn m.p (m.f / m.eX X)
      m.p_ne_two hfe eKX hc
  have hSL : (fr.S : Subgroup G) ≤ L := le_of_odd_relIndex hLn hLodd hSC fr.S.isPGroup'
  have hKXL : m.KX X ≤ L := by
    have := PSL2Sub.isSimpleGroup eKX hfe hr
    have hn : (L.subgroupOf (m.KX X)).Normal := ⟨fun x hx k => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hLn.conj_mem ⟨x, hKXC x.2⟩ hx ⟨k, hKXC k.2⟩⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.subgroupOf (m.KX X)) with hb | ht
    · exfalso
      have hT : fr.T ≤ L ⊓ m.KX X := le_inf (fr.T_le_S.trans hSL) (fr.T_le_KX hXE)
      have hT1 : fr.T = ⊥ := eq_bot_iff.mpr
        (hT.trans (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hb)).le)
      have := fr.isKleinFour_T.card_four
      rw [hT1, Subgroup.card_bot] at this
      omega
    · exact Subgroup.subgroupOf_eq_top.mp ht
  have hKXK'' : m.KX X = K'' := by
    have hle : m.KX X ≤ K'' :=
      calc m.KX X = ⁅m.KX X, m.KX X⁆ := (PSL2Sub.commutator_eq eKX hfe hr).symm
        _ ≤ ⁅Subgroup.zpowers m.J ⊔ K'', Subgroup.zpowers m.J ⊔ K''⁆ := by
          have h1 : m.KX X ≤ Subgroup.zpowers m.J ⊔ K'' := hCL ▸ le_inf hKXL hKXH
          exact Subgroup.commutator_mono h1 h1
        _ ≤ K'' := commutator_zpowers_sup_le (hK''L.trans inf_le_right)
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Nat.card_congr eK''.toEquiv, Nat.card_congr eKX.toEquiv])
  have hLnorm : CX ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLC hLn
  have hLidx := fr.index_ne_two_X hidx hXE eKX hKXL (hcovC.trans hLnorm)
  have hJR : IsJRSubgroup L m.J (m.KX X) m.p (m.f / m.eX X) :=
    ⟨hSL fr.J_mem, m.orderOf_J, by rw [hKXK'']; exact hK''L, by rw [hKXK'']; exact hJK'',
      by rw [hKXK'']; exact hCL, ⟨eKX⟩, hLidx, ⟨fr.S, hSL, fr.isElementaryAbelian_S, fr.card_S⟩⟩
  obtain ⟨hL', hp, hf, -, -⟩ := IsJRSubgroup.nonempty_jrGroup G m.p_ne_two hfe hJR
  have hqL : hL'.q = m.p ^ (m.f / m.eX X) := by rw [JRGroup.q, hp, hf]
  have hsimp : IsSimpleGroup L := by
    by_cases h5 : hL'.q = 5
    · obtain ⟨⟨hs, -⟩, -⟩ := hJ L hL' h5
      exact hs
    · obtain ⟨⟨-, -, hs, -⟩, -⟩ := hR L hL' h5
      exact hs (hqL ▸ hr)
  have hNL : NX ≤ Subgroup.normalizer (L : Set G) :=
    (normalizer_le_normalizer_centralizer X).trans
      (le_normalizer_of_isSimpleGroup hLC hLn hLodd (hSL fr.J_mem) m.J_ne_one (k := 1)
        (by rw [pow_one]; exact m.orderOf_J))
  have hLN : L ≤ NX := hLC.trans hCN
  have hLnN := normal_subgroupOf_of_le_normalizer hNL
  have hST : Nat.card ((fr.S : Subgroup G) ⊓ m.KX X : Subgroup G) = 4 := by
    have : (fr.S : Subgroup G) ⊓ m.KX X = fr.T :=
      le_antisymm (inf_le_inf_left _ inf_le_left) (le_inf fr.T_le_S (fr.T_le_KX hXE))
    rw [this]
    exact fr.card_T
  have key : ∀ x ∈ NX, ∃ l ∈ L, l * x ∈ NX ⊓ m.H := by
    intro x hx
    obtain ⟨l₀, hl₀, hn⟩ := exists_mul_mem_normalizer hLnN hLN fr.S hSL hx
    have hnN : l₀ * x ∈ NX := NX.mul_mem (hLN hl₀) hx
    have hs : l₀ * x * m.J * (l₀ * x)⁻¹ ∈ (fr.S : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp hn m.J).mp fr.J_mem
    have hs1 : l₀ * x * m.J * (l₀ * x)⁻¹ ≠ 1 := fun h1 => m.J_ne_one (by
      have := congrArg (fun z => (l₀ * x)⁻¹ * z * (l₀ * x)) h1
      simpa [mul_assoc] using this)
    obtain ⟨l₁, hl₁, hl₁s⟩ := fr.exists_conj_in_JR m.p_ne_two hfe hJR hSL hST hs hs1
    refine ⟨l₁ * l₀, L.mul_mem hl₁.1 hl₀, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
    · rw [mul_assoc]
      exact NX.mul_mem (hLN hl₁.1) hnN
    · rw [m.mem_H_iff]
      have : l₁ * l₀ * x * m.J * (l₁ * l₀ * x)⁻¹ = m.J :=
        calc l₁ * l₀ * x * m.J * (l₁ * l₀ * x)⁻¹ = l₁ * (l₀ * x * m.J * (l₀ * x)⁻¹) * l₁⁻¹ := by
              group
          _ = m.J := hl₁s
      calc l₁ * l₀ * x * m.J = (l₁ * l₀ * x * m.J * (l₁ * l₀ * x)⁻¹) * (l₁ * l₀ * x) := by
            group
        _ = m.J * (l₁ * l₀ * x) := by rw [this]
  have hJL : Subgroup.zpowers m.J ≤ L := Subgroup.zpowers_le.mpr (hSL fr.J_mem)
  refine ⟨L, ⟨hLC, ⟨hLN, hLnN⟩, ⟨m.KX X, hJR, fun _ => rfl⟩, fun hFX => ?_, fun _ => ?_⟩⟩
  ·
    refine le_antisymm (fun x hx => ?_) (sup_le hLN (fr.E_le_normalizer_of_F_le hXE hFX))
    obtain ⟨l, hl, hy⟩ := key x hx
    have hle : Subgroup.zpowers m.J ⊔ (m.KX X ⊔ fr.EX X) ≤ L ⊔ fr.E :=
      sup_le (hJL.trans le_sup_left) (sup_le (hKXL.trans le_sup_left)
        ((fr.EX_le_E X).trans le_sup_right))
    have := hle (h21 ▸ hy)
    have hx' : x = l⁻¹ * (l * x) := by group
    rw [hx']
    exact (L ⊔ fr.E).mul_mem (Subgroup.mem_sup_left (L.inv_mem hl)) this
  ·
    refine le_antisymm (fun x hx => ?_) (sup_le hLC inf_le_left)
    obtain ⟨l, hl, hy⟩ := key x (hCN hx)
    have hyC : l * x ∈ CX := CX.mul_mem (hLC hl) hx
    have hy' : l * x ∈ (m.KX X ⊔ fr.EX X) ⊔ Subgroup.zpowers m.J := by
      rw [sup_comm, ← h21]
      exact hy
    obtain ⟨w, hw, j, hj, hwj⟩ := (mem_sup_iff_of_le_normalizer
      (fr.zpowers_J_le_normalizer X)).mp hy'
    obtain ⟨k, hk, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer (fr.EX_le_normalizer_KX X)).mp hw
    have hjC : j ∈ CX := hSC ((Subgroup.zpowers_le.mpr fr.J_mem) hj)
    have heC : e ∈ CX := by
      have : e = k⁻¹ * (k * e * j) * j⁻¹ := by group
      rw [this, hwj]
      exact CX.mul_mem (CX.mul_mem (CX.inv_mem (hKXC hk)) hyC) (CX.inv_mem hjC)
    have hx' : x = l⁻¹ * (k * e * j) := by rw [hwj]; group
    rw [hx']
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (L.inv_mem hl))
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (hKXL hk))
        (Subgroup.mem_sup_right ⟨heC, fr.EX_le_E X he⟩)) (Subgroup.mem_sup_left (hJL hj)))

end CFSG.Walter.W67
