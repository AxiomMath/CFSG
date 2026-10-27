module

public import CFSG.Quasithin.Vol2.Asc94.He42P427F
public import CFSG.LocalAnalysis.ZStar
public import CFSG.Quasithin.Vol2.Asc94.He42P427E

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

theorem p427_open427 (T : HeSetup G) (hB : T.BaseFacts) {z : G} (P : P427 T z) :
    ∀ c : G, c * T.a = T.a * c → c ∈ normalizer (T.B : Set G) := by
  classical
  have haZ : T.a ∈ T.Z := T.hD.ha
  have haB : T.a ∈ T.B := T.hD.a_mem_B T.hxN T.hxa T.hx3
  have ha1 : T.a ≠ 1 := p427_a_ne_one T
  obtain ⟨b, hbB, hb1, hba, hbm⟩ := p427_exists_b T
  have hbZ : b ∈ T.Z := hB.B_le_Z hbB
  have hb2 : b * b = 1 := hB.A_sq b (hB.Z_le_A hbZ)
  have haa : T.a * T.a = 1 := hB.A_sq T.a (hB.Z_le_A haZ)
  have hba_comm : b * T.a = T.a * b := hB.A_comm b (hB.Z_le_A hbZ) T.a (hB.Z_le_A haZ)
  have hbM : b ∈ centralizer ({T.a} : Set G) := mem_centralizer_singleton_iff.2 hba_comm
  have hg3 : T.g ^ 3 = 1 := T.hD.g_pow_three T.hxN T.hxa T.hx3
  have hg1 : T.g ≠ 1 := T.hD.g_ne_one T.hxN T.hxa T.hx3
  let t0 : ↥(centralizer ({T.a} : Set G)) := ⟨T.a, mem_centralizer_singleton_iff.2 rfl⟩
  have ht0 : t0 * t0 = 1 := Subtype.ext (by simpa using haa)
  have ht1 : t0 ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hcentM : ∀ h : ↥(centralizer ({T.a} : Set G)), h * t0 = t0 * h := fun h =>
    Subtype.ext (mem_centralizer_singleton_iff.1 h.2)
  haveI hQnorm : (Subgroup.zpowers t0).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g t0 := hcentM g
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact hn
  set Γ := ↥(centralizer ({T.a} : Set G)) ⧸ Subgroup.zpowers t0 with hΓdef
  letI : Fintype Γ := Fintype.ofFinite Γ
  let β : Γ := QuotientGroup.mk ⟨b, hbM⟩
  have hβ1 : β ≠ 1 := by
    intro h
    have h' : (⟨b, hbM⟩ : ↥(centralizer ({T.a} : Set G))) ∈ Subgroup.zpowers t0 :=
      (QuotientGroup.eq_one_iff _).1 h
    rcases p427_mem_zpowers_involution ht0 ht1 h' with h1 | h2
    · exact hb1 (congrArg Subtype.val h1)
    · exact hba (congrArg Subtype.val h2)
  have hβ2 : β * β = 1 := by
    show (QuotientGroup.mk ⟨b, hbM⟩ : Γ) * QuotientGroup.mk ⟨b, hbM⟩ = 1
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    have : (⟨b, hbM⟩ : ↥(centralizer ({T.a} : Set G))) * ⟨b, hbM⟩ = 1 := Subtype.ext (by simpa using hb2)
    rw [this]
    exact Subgroup.one_mem _
  have haM : T.a ∈ centralizer ({T.a} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have haB' : T.a ∈ T.B := haB
  have key1 : ∀ x : G, ∀ hx : x ∈ centralizer ({T.a} : Set G),
      (QuotientGroup.mk ⟨x, hx⟩ : Γ) * β = β * QuotientGroup.mk ⟨x, hx⟩ → x⁻¹ * b * x ∈ T.B := by
    intro x hx hcomm
    have h1 : (QuotientGroup.mk (⟨x, hx⟩ * ⟨b, hbM⟩) : Γ) =
        QuotientGroup.mk (⟨b, hbM⟩ * ⟨x, hx⟩) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hcomm
    have hmem := (QuotientGroup.eq).1 h1
    rcases p427_mem_zpowers_involution ht0 ht1 hmem with h2 | h2
    · have e1 : (x * b)⁻¹ * (b * x) = 1 := by
        have := congrArg Subtype.val h2
        simpa using this
      have e2 : x⁻¹ * b * x = b := by
        calc x⁻¹ * b * x = b * ((x * b)⁻¹ * (b * x)) := by group
          _ = b := by rw [e1, mul_one]
      rw [e2]
      exact hbB
    · have e1 : (x * b)⁻¹ * (b * x) = T.a := by
        have := congrArg Subtype.val h2
        simpa using this
      have e2 : x⁻¹ * b * x = b * T.a := by
        calc x⁻¹ * b * x = b * ((x * b)⁻¹ * (b * x)) := by group
          _ = b * T.a := by rw [e1]
      rw [e2]
      exact T.B.mul_mem hbB haB
  have key2 : ∀ x : G, x ∈ centralizer ({T.a} : Set G) → x⁻¹ * b * x ∈ T.B →
      x ∈ normalizer (T.B : Set G) := by
    intro x hx hxb
    have hxa : x * T.a = T.a * x := mem_centralizer_singleton_iff.1 hx
    have hxinv : x⁻¹ ∈ normalizer (T.B : Set G) := by
      apply Subgroup.mem_normalizer_fintype
      intro y hy
      rcases T.hD.B_elems T.hxN T.hxa T.hx3 hbB hb1 hba y hy with rfl | rfl | rfl | rfl
      · have e : x⁻¹ * 1 * x⁻¹⁻¹ = 1 := by group
        rw [e]
        exact T.B.one_mem
      · have e : x⁻¹ * T.a * x⁻¹⁻¹ = T.a := by
          rw [inv_inv]
          calc x⁻¹ * T.a * x = x⁻¹ * (T.a * x) := by group
            _ = x⁻¹ * (x * T.a) := by rw [← hxa]
            _ = T.a := by group
        rw [e]
        exact haB
      · rw [inv_inv]
        exact hxb
      · rw [inv_inv]
        have e : x⁻¹ * (T.a * b) * x = T.a * (x⁻¹ * b * x) := by
          calc x⁻¹ * (T.a * b) * x = (x⁻¹ * T.a * x) * (x⁻¹ * b * x) := by group
            _ = T.a * (x⁻¹ * b * x) := by
              congr 1
              calc x⁻¹ * T.a * x = x⁻¹ * (T.a * x) := by group
                _ = x⁻¹ * (x * T.a) := by rw [← hxa]
                _ = T.a := by group
        rw [e]
        exact T.B.mul_mem haB hxb
    have := inv_mem hxinv
    rwa [inv_inv] at this
  have hiso : ∀ g : Γ, (g * β * g⁻¹) * β = β * (g * β * g⁻¹) → g * β * g⁻¹ = β := by
    intro g hg
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective g
    have hcM : x * b * x⁻¹ ∈ centralizer ({T.a} : Set G) :=
      (centralizer ({T.a} : Set G)).mul_mem ((centralizer ({T.a} : Set G)).mul_mem hx hbM)
        ((centralizer ({T.a} : Set G)).inv_mem hx)
    have hgc : (QuotientGroup.mk ⟨x, hx⟩ : Γ) * β * (QuotientGroup.mk ⟨x, hx⟩)⁻¹ =
        QuotientGroup.mk ⟨x * b * x⁻¹, hcM⟩ := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
    rw [hgc] at hg ⊢
    have hcomm : (QuotientGroup.mk ⟨x * b * x⁻¹, hcM⟩ : Γ) * β =
        β * QuotientGroup.mk ⟨x * b * x⁻¹, hcM⟩ := hg
    have hc1 := key1 (x * b * x⁻¹) hcM hcomm
    have hcN := key2 (x * b * x⁻¹) hcM hc1
    have hcB := p427_isol T hB P.hL P.hLcard P hbB hb1 hba hbm hx hcN
    rcases T.hD.B_elems T.hxN T.hxa T.hx3 hbB hb1 hba _ hcB with h1 | h1 | h1 | h1
    · exfalso
      apply hb1
      calc b = x⁻¹ * (x * b * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group
    · exfalso
      apply hba
      calc b = x⁻¹ * (x * b * x⁻¹) * x := by group
        _ = x⁻¹ * T.a * x := by rw [h1]
        _ = T.a := by
          calc x⁻¹ * T.a * x = x⁻¹ * (T.a * x) := by group
            _ = x⁻¹ * (x * T.a) := by rw [← mem_centralizer_singleton_iff.1 hx]
            _ = T.a := by group
    · congr 1
      exact Subtype.ext h1
    · have hel : (⟨x * b * x⁻¹, hcM⟩ : ↥(centralizer ({T.a} : Set G))) =
          ⟨T.a, haM⟩ * ⟨b, hbM⟩ := Subtype.ext (by simp [h1])
      have ha1' : (QuotientGroup.mk ⟨T.a, haM⟩ : Γ) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers t0)
      show (QuotientGroup.mk ⟨x * b * x⁻¹, hcM⟩ : Γ) = QuotientGroup.mk ⟨b, hbM⟩
      rw [hel, QuotientGroup.mk_mul, ha1', one_mul]
  obtain ⟨N, hNn, hNodd, hNc⟩ := CFSG.ZStar.glauberman_zStar Γ β hβ1 hβ2 hiso
  haveI := hNn
  have hK : ∀ K : Subgroup ↥(centralizer ({T.a} : Set G)),
      (∀ h : ↥(centralizer ({T.a} : Set G)), ∀ k ∈ K, h * k * h⁻¹ ∈ K) →
        Odd (Nat.card ↥K) → K = ⊥ := by
    intro K hKn hKodd
    let KG : Subgroup G := K.map (centralizer ({T.a} : Set G)).subtype
    have hKGM : KG ≤ centralizer ({T.a} : Set G) := by
      rintro _ ⟨k, -, rfl⟩
      exact k.2
    have hKGn : ∀ m ∈ centralizer ({T.a} : Set G), ∀ o ∈ KG, m * o * m⁻¹ ∈ KG := by
      rintro m hm _ ⟨k, hk, rfl⟩
      exact Subgroup.mem_map.2 ⟨⟨m, hm⟩ * k * (⟨m, hm⟩)⁻¹, hKn _ k hk, by simp⟩
    have hKGodd : Odd (Nat.card ↥KG) := by
      rw [Subgroup.card_map_of_injective Subtype.val_injective]
      exact hKodd
    have hbot := p427_O_trivial T hB P KG hKGM hKGn hKGodd
    have hcard : Nat.card ↥K = 1 := by
      have h1 : Nat.card ↥KG = Nat.card ↥K := Subgroup.card_map_of_injective Subtype.val_injective
      rw [← h1, hbot, Subgroup.card_bot]
    exact Subgroup.eq_bot_of_card_eq K hcard
  have hNbot : N = ⊥ := p427_zstar_trivial t0 ht0 ht1 hcentM N hNodd hK
  intro c hc
  have hcM : c ∈ centralizer ({T.a} : Set G) := mem_centralizer_singleton_iff.2 hc
  have hgN := hNc (QuotientGroup.mk ⟨c, hcM⟩)
  rw [hNbot, Subgroup.mem_bot] at hgN
  have hcomm : (QuotientGroup.mk ⟨c, hcM⟩ : Γ) * β = β * QuotientGroup.mk ⟨c, hcM⟩ := by
    have h1 := mul_inv_eq_one.1 hgN
    have h2 := mul_inv_eq_iff_eq_mul.1 h1
    exact h2
  exact key2 c hcM (key1 c hcM hcomm)

end CFSG.Quasithin.A94.He42
